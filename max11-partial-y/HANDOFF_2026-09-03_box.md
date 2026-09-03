# Max-11 coordinator handoff — 2026-09-03 (migration to the AWS box)

The campaign loop now runs ON the box (`ubuntu@54.81.66.156`, r6i.4xlarge), so the
Mac can be offline. Everything below is in `~/coord` on the box.

## Layout on the box
- `~/coord/jc2-lean` — coordinator clone (origin = `git@github.com:dcposch/jc2-lean.git`
  via the `box-lean-coordinator` deploy key, push allowed). Untracked scratch drafts and
  `.max11-lanes/gates` receipts were rsynced from the Mac on 2026-09-03.
- `~/jc2-lean/max11-partial-y` — the VERIFIER build root (Mathlib oleans + 13G scratch
  olean cache). Never edit by hand; `box_lean_verify.sh` rsyncs into `box-lean-verify.*`.
- `~/coord/env.sh` — source it in every shell: nvm/node, grok, and
  `BOX_LEAN_HOST=ubuntu@localhost BOX_LEAN_KEY=~/.ssh/id_ed25519
  BOX_LEAN_DIR=/home/ubuntu/jc2-lean/max11-partial-y MAX11_DIR=~/coord/jc2-lean/max11-partial-y
  MAX11_LANE_LOGS=~/coord/lanes`.
- `~/coord/lanes/*.log` + `pid_targets.txt` — lane logs and pid→target map.
- Credentials: `~/.grok/auth.json` (grok 4.6), `~/.claude/.credentials.json` (Claude Code).

## Coordinator scripts (tracked, `max11-partial-y/scripts/coord/`)
- `launch_lane.sh Target.lean logname "instruction"` — direct-launch a Grok lane with the
  contract (8-worker cap, foreground verify required).
- `wait_event.sh [secs]` — block until a lane exits or a receipt lands.
- `harvest.sh File.lean` — is the file green at its current SHA? list its final theorems.
- `green_untracked.sh` — sweep untracked scratch for green receipts.
- `promote_closure.py MODULE...` — import closure of a leaf closure for lakefile promotion.
- `build_max11_package.py --src max11-partial-y --comp gcd3-69-composition --out DIR` —
  the single-package Palomar layout (validated 2026-09-02: 9387 jobs, standard axiom trio).

## Live state (2026-09-03 09:00Z) — see `LANE_QUEUE_2026-09-03.md` for the full queue
- (4,6) (6,9) (4,10) closed and in the library.
- (6,8): scale two CLOSED (`planeKellerNormalized68ScaleTwoRoute_closed`); scale zero = ONE
  cell (`FiveToSixTerminalZeroMeetingCell68`), plan in `Grok68TerminalZeroMeetingCellPlanScratch.md`,
  lane `Grok68TerminalZeroMeetingCellScratch` in flight.
- (6,10): scale two CLOSED (`planeKellerNormalized610LowScaleRoute_of_scaleZero`); scale zero =
  ratio-tie cones, lane `Grok610ScaleZeroConeFinishScratch` in flight (LC-power certificates).
- (8,10): glue + chamber split landed; aligned-nonsquare CLOSED; scale zero = mixed cones
  (`Grok810ScaleZeroConeExhaustionScratch` in flight); aligned-square = tower C+T draft
  `Grok810AlignedSquareClearedNumeratorFixScratch` (emitter bug in block-lemma headers) then Z;
  nonzero face = `Grok810NonzeroFaceClosureScratch` (12.5k lines, written, gate pending).
- Endgame: per-leaf `proved_planeKellerNormalized{68,610,810}LowScaleRoute` → headline
  `Max11PlaneKellerGenerationWithFourNormalizedRoutesAfterClosed410` modulo the two classical
  citations → promotion (lakefile roots + Max11Assembly import, full build) → package → Palomar.

## Rules
- Commit only receipt-verified green scratch (`git add -f`), push to master, never bulk-add.
- Scratch is content-keyed; committing scratch never disturbs live gates.
- Nonsquare aligned chambers: primitive + ODE lemma (`quadraticCoreOde_no_polynomial_solution610`),
  never Newton-limb descent. Non-converging row attacks → integrate the last Keller row into a
  weight-(m+n-1) primitive and run a bounded pole tower.
- Lanes must verify in the FOREGROUND; if a lane dies mid-verify, the coordinator reruns
  `./scripts/box_lean_verify.sh --file F` itself with `BOX_LEAN_COMPILE_TIMEOUT_SECONDS=21600`.

## Mac side final (2026-09-03 11:30Z)
- All Mac lanes are stopped. The Mac harvested nothing after commit 0c79552. Nothing is
  pending on the Mac.
- The four Mac-owned drafts are in this clone at their final state; none is green at its final
  SHA. Relaunch each from its draft (or gate it first): `Grok610ScaleZeroConeFinishScratch`
  (3610 L, last green at SHA 8325db59), `Grok68TerminalZeroMeetingCellScratch` (2047 L, last
  green 3edc31bb), `Grok810ScaleZeroConeExhaustionScratch` (2889 L, last green df3d8fa8 of its
  parent only), `Grok810NonzeroFaceClosureScratch` (12508 L, never gated; needs a 6 h gate).
- All 807 Mac receipts are in `.max11-lanes/gates` here.
- The stale CAS job `verify_68_degree_zero_h0_row.py` was killed 2026-09-03 11:25Z; obsolete.
- Palomar browser step (GitHub sign-in, register click) is DC's; hand DC the package path and
  the 40-char SHA when the package is built and axiom-audited.
