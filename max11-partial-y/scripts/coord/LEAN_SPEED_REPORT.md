# Tier 1 — making Max-11 emitted proof files compile in minutes

Author: lean-speed seat, 2026-09-03.  All numbers measured on the campaign
AWS box (16 vCPU r6i.4xlarge) through the sanctioned verifier
`scripts/box_lean_verify.sh --file … --profile`, every compile under
`nice -n 15`, never more than two of ours at a time, while the live Max-11
gates were running.  Contention therefore inflates *all* wall times below,
baseline included, by roughly 1.6x versus an idle box (the baseline file's
historical uncontended time is 21.4 min; we measured 35.1 min today).

## 1. Benchmark

`Fable810ScaleZeroEleventhDefectScratch.lean` — 2 640 lines, **tracked and
green**, chosen from the metrics ledger as a mid-size representative of the
slowest family in the corpus (`Fable*ScaleZero*DefectScratch`, whose largest
member `Fable810ScaleZeroFourteenthDefectScratch.lean` took **273 min**).

Its cost is concentrated in one declaration,
`twelfthDefect_eq_clearedMu810`: sixteen `have hX : depressedX810 … = N_X /
(d_X · h^{e_X})` hypotheses, then

```lean
  simp only [muResidual810, hL, hA, …, etaResidual810]
  field_simp [hh, h2, h4, …, hh84]
  ring
```

Copied verbatim to `SpeedBenchBaselineScratch.lean` (full file) and
`SpeedBenchMonsterBaseScratch.lean` (that declaration alone, 517 lines).

## 2. Where the time actually goes  ← the headline result

Lean `--profile` totals:

| phase | full file (35.1 min) | monster only (28.4 min) |
|---|---:|---:|
| **linting** | **663 s** | **686 s** |
| **type checking (kernel)** | **713 s** | **531 s** |
| typeclass inference | 461 s | 222 s |
| elaboration | 190 s | 32 s |
| fix level params | 120 s | 120 s |
| `field_simp` (interpretation) | 64 s | 55 s |
| `ring` | 24 s | 12 s |
| `simp` | 24 s | 0.3 s |
| share common exprs | 24 s | 21 s |
| .olean serialization | 10 s | 14 s |
| blocked (unaccounted, parallel wait) | 944 s | — |

**Nobody had profiled this, and the folk model was wrong.**  `field_simp` and
`ring` together are ~1.5 min of a 28-minute declaration (4 %).  The compile is
dominated by two things that scale with the *size of the proof term* `ring`
produces, not with the time `ring` spends producing it:

1. **Linting (40 % of the monster).**  Lean's and Mathlib's syntactic linters
   walk the `InfoTree` of the finished declaration.  A `ring` proof of a
   250-monomial identity has an enormous `InfoTree`.  This work is pure
   diagnostics — it contributes nothing to the proof.
2. **Kernel type checking (31 %).**  The kernel re-checks `ring`'s reflection
   certificate.  This is genuine assurance and must be paid, but its cost is
   superlinear in the monomial count, so it shrinks fast when the identity is
   split into blocks.

The remaining large items (`typeclass inference`, `fix level params`,
`share common exprs`, `.olean serialization`) also scale with proof-term size.

## 3. Experiments

Each experiment is its own `SpeedBench*Scratch.lean` in `$MAX11_DIR`, proving
the **same theorem statement** `twelfthDefect_eq_clearedMu810` from the same
hypotheses.

| id | file | change |
|---|---|---|
| B0 | `SpeedBenchBaselineScratch.lean` | verbatim copy of the tracked file |
| B1 | `SpeedBenchMonsterBaseScratch.lean` | the one costly declaration, alone |
| L  | `SpeedBenchNoLintScratch.lean` | B1 + nine `set_option linter.… false` |
| C  | `SpeedBenchClearedScratch.lean` | cleared two-stage proof, no big `field_simp` |
| CR | `SpeedBenchClearedCRScratch.lean` | C, cleared polynomial `def` restated over `[CommRing K]` w/ integer coeffs |
| K  | `SpeedBenchBlkOneFileScratch.lean` | C + 8-block split, all in one module |
| M  | `SpeedBenchBlk{Defs,00..07,Agg}Scratch.lean` | C + 8-block split, one module per block, linters off |

### (a) Cleared form — remove the big `field_simp` entirely

The compact residual `mu` is **weighted homogeneous** of weight 12 with
`weight(X_i) = e_i / 7`.  So substituting `X_i := n_i / (d_i h^{e_i})` makes

```
    2^34 · h^84 · mu(X_L, …, X_W)
```

a *polynomial* in `h, n_L, …, n_W` — 68 monomials.  (sympy confirms this in
3.6 s; Lean's `field_simp` was spending 55 s rediscovering it on the fully
expanded polynomials.)  The emitted proof is therefore two stages:

```lean
theorem speedMuScaled810_eq (h : F) (hh : h ≠ 0) (nL … nW : F) :
    (17179869184 : F) * h ^ 84 * muResidual810 (nL / 4) (nA / (16 * h ^ 14)) … =
      speedMuScaled810 h nL … nW := by
  simp only [muResidual810, alphaResidual810, …, speedMuScaled810]
  field_simp            -- 17 atoms only; cheap
  ring

theorem twelfthDefect_eq_clearedMu810 … := by
  have hL … ; have hW0 …            -- unchanged
  rw [hL, hA, …, hW0, speedMuScaled810_eq h hh]
  simp only [speedMuScaled810]
  ring                              -- one polynomial ring, no division
```

### (b) `linear_combination`

Not applicable in the useful direction here.  `linear_combination` needs the
cofactors of the sixteen cleared hypotheses; those cofactors are themselves
polynomials of the same size as the expanded identity, so emitting them costs
exactly what it saves, and `linear_combination`'s own `ring1` then runs on a
goal *larger* than the one `ring` already sees after (a).  We measured the
degenerate form `linear_combination (0 : F)` as a `ring1` proxy instead.

### (c) `grind`, `ring1`, `ring_nf`

Measured as drop-in replacements for the final `ring` of recipe (a).

### (d) Module splitting

The 68-monomial cleared polynomial is split into 8 blocks of ~9 monomials.
The CAS pre-computes each block's expansion in the source variables, so each
block is one small `ring` in its own module.  Note the verifier
`box_lean_verify.sh` composes a *scratch import closure* and compiles it with
`&&` — **serially within one invocation**.  Parallelism therefore comes from
running one `--file` invocation per block module; the content-keyed olean
cache then makes the aggregator's gate report `SCRATCH_CACHE_HIT` for every
block and elaborate only the aggregation step.  A one-block edit invalidates
one block key plus the aggregator's.

## 4. Results

All wall times measured today, on the shared box, with 2-4 campaign gates
running concurrently.  Axioms checked by `#print axioms
twelfthDefect_eq_clearedMu810`, recorded in the verifier output.

| id | variant | wall | CPU s | max RSS | axioms | vs B1 |
|---|---|---:|---:|---:|---|---:|
| B0 | full tracked file, verbatim | 35.07 m | 1966 | 10.04 GiB | clean | — |
| B1 | the one declaration, verbatim | **28.42 m** | 1460 | 9.34 GiB | clean | 1.00x |
| L  | B1 + linters off (9 `set_option`s) | **16.02 m** | 958 | 9.35 GiB | clean | **1.77x** |
| C  | cleared two-stage, linters ON | **4.72 m** | 309 | 8.23 GiB | clean | **6.02x** |
| **R1+R2** | **C + linters off (recommended)** | **~4.65 m†** | ~309 | ~8.23 GiB | clean | **~6.1x** |
| CR | C, `speedMuScaledInt810` over `[CommRing K]`, integer coeffs | 4.65 m | 306 | 8.21 GiB | clean | 6.11x |
| C-linear_combination0 | C, final `linear_combination (0 : F)` | 4.98 m | 341 | 8.22 GiB | clean | 5.71x |
| C-ring1 | C, final `ring1` | 5.38 m | 366 | 8.23 GiB | clean | 5.28x |
| C-ring_nf | C, final `ring_nf` | 5.82 m | 359 | 8.23 GiB | clean | 4.88x |
| C-grind | C, final `grind +ring` | 6.62 m | 427 | 8.22 GiB | **sorryAx (FAILED)** | — |
| K | C + 8-block split, blocks **in one module**, linters off | 13.78 m | 883 | 8.76 GiB | clean | 2.06x |
| M-defs | shared block-defs module alone (see §4(d)) | 12.79 m | 687 | 7.49 GiB | n/a | — |
| M-agg | 8-block-per-module split, aggregator (cold) | 5.65 m | 330 | 7.85 GiB | clean | 5.03x |
| M total | **M-defs + 8 blocks (2-at-a-time) + M-agg, cold, end-to-end** | **~20.0 m** | ~1166 | 7.85 GiB | clean | 1.42x |

`clean` = axioms ⊆ `{propext, Classical.choice, Quot.sound}` (every row above uses
all three except the smoke test in §Emitter, which is fine — `⊆`, not `=`, is
the actual Palomar requirement).  †R1+R2's wall time was not compiled as a
separate file: the Phase breakdown just below shows C's own linting is
already 4.3 s of 309 s CPU (R2 already collapsed the `InfoTree` R1 targets),
so adding R1's nine `set_option`s to C saves at most that 4.3 s — within
run-to-run box-load noise, hence "~".  This is the recommended recipe; see
§7.

### Phase breakdown of the winners

| phase | B1 (28.4 m) | L (16.0 m) | C (4.7 m) |
|---|---:|---:|---:|
| linting | 686 s | **0.03 s** | 4.3 s |
| type checking | 531 s | 505 s | **6.0 s** |
| typeclass inference | 222 s | 219 s | 241 s |
| fix level params | 120 s | 102 s | 1.1 s |
| `field_simp` | 55 s | 55 s | 11 s |
| `ring` | 12 s | 12 s | 7 s |
| elaboration | 32 s | 29 s | 26 s |

Reading:

* **L** proves the linting diagnosis exactly: 686 s -> 0.03 s, nothing else
  moves, wall drops 1.77x.  Nine lines, no risk, no CAS work.
* **C** is the structural fix.  Restating the identity so that `ring` sees one
  *polynomial* goal instead of a `field_simp` normal form collapses the proof
  term: kernel type checking 531 s -> 6 s (88x), `fix level params` 120 s ->
  1 s, and linting falls out for free (686 s -> 4 s) because there is far less
  `InfoTree` to walk.  This is why C beats L even with the linters left on.
* What is left in C is **typeclass inference (241 s of 309 s CPU)** --
  resolving `OfNat F c`, `HMul`, `HPow` once per monomial while elaborating
  ~300 monomials over an abstract `[Field F] [CharZero F]`.  That is now the
  entire remaining cost, which motivated the CR experiment below.
* **CR — measured, and the hoped-for typeclass win did not appear.**
  `SpeedBenchClearedCRScratch.lean` restates the cleared polynomial,
  `speedMuScaledInt810`, with integer coefficients over `{K : Type*}
  [CommRing K]` (the tracked `Grok810AlignedSquare…Repair` file already writes
  its block `def`s that way).  Measured: **4.65 m**, typeclass inference
  **237 s** -- essentially unchanged from C's 241 s.  The reason is structural,
  not a measurement fluke: only the small atom-clearing lemma
  (`speedMuScaled810_eq`) is stated over the shallow `CommRing K` instance;
  the *main* declaration `twelfthDefect_eq_clearedMu810` still elaborates its
  ~300-monomial goal over `[Field F] [CharZero F]` because its target (the RHS
  in the tracked theorem statement) is a field-valued expression that the CAS
  cannot restate as an integer polynomial without also changing what the
  calling proof lane's hypotheses provide.  The 237 s of typeclass inference
  lives in that final `ring`, not in the small lemma CR shortens, so CR nets
  only the ~1.5% you'd expect from shaving a few seconds off a 5-minute
  compile.  A CommRing rewrite only pays if the *entire* declaration —
  including the target — can be restated as an integer identity, which is a
  per-identity CAS decision, not something the emitter can default to.

### (d) Module splitting: measured, and it does NOT pay at this size

Splitting the 68-monomial cleared polynomial into 8 blocks and pre-expanding
each block with the CAS produces **~950 monomials of block expansions where
the unsplit identity has 252** -- the cancellation between blocks is global,
so each block's expansion carries terms that die in the sum.  Since the
residual cost is proportional to monomial count (typeclass inference during
elaboration), splitting multiplies the total work by ~3.8x and only wins if
the parallel speedup exceeds that.

Measured: the shared definitions module `SpeedBenchBlkDefsScratch.lean` alone
took **12.79 m** (652 s of it typeclass inference), already worse than the
whole unsplit recipe C at 4.72 m.  Splitting is therefore **not recommended
below roughly a thousand monomials**; above that the kernel/`ring` cost
becomes superlinear again and the trade flips.

Two structural corrections that follow from this measurement and are now
implemented in the emitter (`~/lean/tools/lean-speed/emit/lean_speed.py`):

1. Put each block's *expansion* `def` in that block's own module, not in the
   shared definitions module -- otherwise the whole ~950-monomial elaboration
   sits on the serial critical path in front of every block.
2. State the polynomial `def`s over `{K : Type*} [CommRing K]` with integer
   coefficients (scale the identity by the lcm of the coefficient
   denominators, 64 here) rather than over `[Field F] [CharZero F]`.

**End-to-end, measured.**  With correction (1) applied (`SpeedBenchBlk00..07
Scratch.lean`, one small `def`+`ring` module each, 16-26 CPU-s / 18-26 s wall
apiece) plus `SpeedBenchBlkDefsScratch.lean` (shared defs, serial
prerequisite for every block) plus `SpeedBenchBlkAggScratch.lean` (the
aggregator, serial, needs every block):

| stage | wall | note |
|---|---:|---|
| `BlkDefs` (serial prerequisite) | 12.79 m | must finish before any block starts |
| 8 blocks, run 2-at-a-time (`MAXMINE=2`) | ~1.5 m | measured per block 0.29-0.44 m; 4 pairs, pair time ≈ slower block, not the sum -- blocks are too short for real overlap to matter |
| `BlkAgg` (serial, needs all 8 blocks) | 5.65 m | one `simp`/`rw` chain then one flat `ring` over the 68-monomial sum |
| **total, cold** | **~20.0 m** | vs C's 4.72 m: **4.2x slower**, vs B1's 28.4 m: 1.42x faster |

Module splitting is a net loss against the recommended recipe (R1+R2) at this
identity's size, confirming the monomial-count argument above with an actual
compile rather than just the `BlkDefs` component.

**Single-block edit, measured.**  Edited one comment line into
`SpeedBenchBlk00Scratch.lean` (a no-op content change, enough to invalidate
its content-addressed cache key and everything importing it) and re-verified
only the changed block plus the aggregator, leaving `BlkDefs` and blocks
01-07 as cache hits:

| step | wall | CPU s |
|---|---:|---:|
| `Blk00` (edited, forced recompile) | 0.31 m | 17.1 |
| `BlkAgg` (recompiled: imports the changed `Blk00`) | 4.33 m | 258.3 |
| **total re-verify** | **4.64 m** | 275.4 |

The edit-then-reverify cost (4.64 m) is essentially the same as recompiling
recipe C **from scratch** (4.72 m), because the aggregator's own `ring` --
closing the flat 68-monomial sum -- costs almost as much on its own as the
*entire* unsplit cleared proof.  At this identity's size, module splitting
buys no incremental-edit advantage either: the bottleneck moved from "the one
big declaration" to "the aggregator," which still has to see the whole
identity.  Splitting only starts to pay once the aggregator's own `ring` is
cheap relative to what it replaces -- i.e. the "roughly a thousand monomials"
threshold above, where R3 is worth revisiting.

## 5. What did NOT work, and why

* **Blaming `field_simp` and `ring`.**  The whole premise that these files are
  slow because of the tactic search is false for this corpus.  On the
  benchmark declaration `field_simp` is 55 s and `ring` is 12 s out of 1 704 s
  (4 % combined).  Any Tier-1 effort aimed only at the tactics can win at most
  a few percent.  Measure before optimising the next family too.
* **`linear_combination` with explicit cofactors.**  Rejected on paper: the
  cofactors of the sixteen cleared hypotheses are polynomials of the same
  order as the expanded identity, so emitting them roughly doubles the file
  and hands `ring1` a strictly larger goal than recipe (a) already produces.
  `linear_combination (exp := n)` is for goals that need a power of the
  hypothesis, which is not this shape.
* **`grind` / `grind +ring`.**  `grind` is a saturating prover; on a
  250-monomial commutative-ring identity it has nothing to saturate over and
  falls back to its ring core without `ring`'s Horner normalisation.  Measured
  anyway (see table); it is not competitive, and it is worse than merely
  slow: `#print axioms` on the resulting theorem reports
  `[propext, sorryAx, Classical.choice, Quot.sound]` -- `grind` left the goal
  open and Lean's elaborator silently inserted a `sorry`, while `BUILD_EXIT=0`
  and `ERROR_COUNT=0` made the compile *look* clean.  Any pipeline trusting
  build-exit-code alone for this tactic would ship an unproved theorem;
  `#print axioms` on the final aggregated theorem (§8, point 4) is not
  optional.
* **`ring_nf`.**  Normalises both sides but leaves the goal for `rfl`; it
  produces a *larger* proof term than `ring` for a pure identity, which is
  exactly the quantity we are trying to shrink.
* **CommRing integer coefficients (CR), on the *whole* declaration.**  Stating
  only the intermediate cleared-polynomial `def` over `[CommRing K]` (§4,
  `SpeedBenchClearedCRScratch.lean`) saves ~1.5%, not the large win the
  "shallower instance graph" hypothesis predicted, because the 237 s of typeclass
  inference lives in the *final* `ring`, which still elaborates over
  `[Field F] [CharZero F]` since the theorem's target is a field expression
  supplied by the calling proof lane.  CR only pays if the target itself can
  also be restated as an integer identity -- a per-identity CAS decision.
* **Module splitting below ~1000 monomials, checked twice.**  Not only does
  the component measurement (`BlkDefs` alone, 12.79 m) already exceed C's
  4.72 m; the full cold end-to-end compile (~20.0 m) and the single-block
  incremental-edit cost (4.64 m, see §4(d)) both confirm it.  The aggregator's
  own `ring` costs almost as much as the whole unsplit proof, so splitting
  neither wins on a cold build nor on an incremental edit at this size.
* **All 8 blocks in one module (K), instead of one module per block.**
  13.78 m -- faster than the 8-modules-plus-aggregator total (~20.0 m,
  because there is no `BlkDefs`/import overhead repeated per file) but still
  3x C, and it forfeits the entire point of splitting: one file means one
  verifier invocation, so an edit to any block recompiles the whole 13.78 m
  file, same as not splitting at all.
* **Multiple `--file` arguments in one verifier invocation.**  The script
  accepts them, but it composes one remote Bash program joining every module
  with `&&`, so they compile **serially**.  Parallelism must come from
  separate invocations (which is safe: each takes a distinct per-target lock
  and the content-addressed cache uses `flock` per key).
* **Raising `maxHeartbeats` further.**  Irrelevant.  Heartbeats bound
  elaboration, and elaboration is not the bottleneck; the kernel and the
  linters are not heartbeat-limited at all.

## 6. Ideas for Tier 2 (not attempted, as instructed)

* **A reflective kernel-`decide` ring checker.**  A certificate that is
  *checked* rather than *recomputed* would attack the 531 s / 237 s of kernel
  `type checking` and typeclass inference directly: emit a reflected
  polynomial representation (coefficient lists, not `HMul`/`HPow`-laden
  terms) from the CAS, and have `decide` (evaluated *in the kernel*, on a
  `Decidable` instance built from `Bool`-returning normalisation, not
  `Lean.ofReduceBool`) certify that the two reflected polynomials are equal.
  `Mathlib.Tactic.Polyrith`'s certificate shape and `ring`'s own
  `Mathlib.Tactic.Ring.Basic` reflection are the models.  **Important:** this
  is plain kernel `decide`, not `native_decide` -- `native_decide` compiles
  the decision procedure to native code and trusts that compiler via
  `Lean.ofReduceBool`, which is an *extra* axiom.  Palomar permits only
  `propext`, `Classical.choice`, `Quot.sound`, so `native_decide` (and
  anything using `Lean.ofReduceBool`) is categorically forbidden for Max-11
  regardless of speed; only ordinary, kernel-checked `decide` is admissible,
  and even that must stay fast enough not to blow the kernel's own reduction
  budget on a 300-monomial polynomial (untested — a real Tier-2 spike, not a
  Tier-1 result).
* `ring`'s certificate for `p = q` with `p`, `q` already flat sums of
  monomials is pure commutativity/associativity bookkeeping.  A dedicated
  `sorted_monomials` decision procedure emitting a permutation certificate
  would make the *aggregation* step (the only step whose size is the full
  identity, per §4(d)'s finding that `BlkAgg`'s own `ring` is the real
  splitting bottleneck) essentially free -- this is what would let module
  splitting (R3) start paying off below the ~1000-monomial threshold
  measured in §4(d), since it's the aggregator, not the blocks, that is
  currently too expensive.
* The linter cost is a Lean/Mathlib-side issue: a `set_option
  linter.skipLargeDeclarations` style gate (skip InfoTree walks for
  declarations above a size threshold) would help every generated file in the
  ecosystem, not just Max-11.  (Measured: R2 already makes this moot for
  identities in the Max-11 size range, since clearing on atoms collapses the
  `InfoTree` before any linter walks it -- see §4 phase breakdown.)

## 7. Recommended recipe

Apply R1 and R2 always; R1 alone is a one-line change a lane can adopt today
with no CAS work at all.  **R3 (module splitting) is conditional** — measured
in §4(d) to be a **net loss** below roughly a thousand monomials in the
cleared polynomial (this benchmark's 68/252-monomial identity: ~20.0 m
split vs. 4.72 m unsplit, both cold and on a single-block edit) — apply it
only once a CAS-side monomial count crosses that threshold, or once the
Tier-2 aggregation-certificate idea (§6) removes the aggregator's own `ring`
as the bottleneck.

**R1 — turn the linters off in every generated file.**  Immediately after the
`namespace` line of any emitted `*Scratch.lean`:

```lean
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
```

These are diagnostics only.  They change no term, no proof and no axiom, and
a machine-generated file has no audience for them.

**R2 — clear on the atoms, never on the expanded polynomials.**  Have the CAS
emit the weighted-homogeneous cleared form `scale · h^p · compact(n_i/(d_i
h^{e_i}))` as an explicit `def` over the numerator atoms, prove that one
small `field_simp` lemma over the atoms, and let the main proof be
`rw [hL, …, hW0, <lemma> h hh]; simp only [<def>]; ring`.  No `field_simp`
ever touches an expanded polynomial again.

**R3 — above ~1000 cleared monomials only: split into ~10-monomial blocks,
one module per block.**  The CAS pre-computes each block's source expansion,
so every block is one small `ring`, the kernel checks many small
certificates instead of one big one, and the blocks compile in parallel as
separate verifier invocations.  The aggregator then only rewrites the blocks
and closes a flat sum — but that final sum is itself one `ring` over the
*whole* identity (§4(d)), so R3 only wins once the identity is large enough
that eight-plus small certificates plus one aggregation are cheaper than one
big one; below that threshold (this benchmark included) skip R3 and stop at
R2.

`~/lean/tools/lean-speed/emit/lean_speed.py` implements R1-R3 mechanically —
give it named polynomial identities and denominators to clear and it emits
the definitions module, one block module per identity, and the aggregator;
see its `README.md` for the spec format and the CLI.  `--block-size` controls
R3: below the ~1000-monomial threshold, pass a `--block-size` at least as
large as the cleared identity's monomial count (so the emitter produces
exactly one block per identity — R1+R2 with no real R3 overhead); above the
threshold, use the default (10) or tune it.

**Emitter, tested end-to-end.**  `lean_speed.py` (plus `leanprint.py`,
`leanparse.py`) was exercised on a throwaway two-monomial toy identity
(`Atom`/`Identity`/`EmitConfig`, `block_size=1`): it produced a defs module,
two block modules and an aggregator, all four compiled clean on the first
try in one verifier invocation (`box_lean_verify.sh --file
<agg>.lean`, which pulls in its whole import closure), and `#print axioms`
on the aggregated theorem reported a subset of the three permitted axioms.
Two real bugs surfaced and were fixed in the emitter and documented in the
README:
1. The aggregator module never printed `#print axioms` despite the
   already-defined `EmitConfig.axioms` flag going unused — fixed; the
   aggregator now ends with `#print axioms <ns>.<name>Cleared_eq_expansion`
   whenever `axioms=True` (the default).
2. If `Identity.hvar` (the CAS's `h`-like scaling variable) is not also
   listed in `Identity.src`, the emitted block and aggregator theorems
   reference `hvar` as a free, unbound identifier — Lean would reject the
   generated file.  Every real Max-11 spec already includes `hvar` in `src`
   (`bench_model.py`'s `SRC` starts with `h`), so this never bit production
   use, but a spec author following the README without that convention would
   have hit a silent bad-codegen bug.  `Identity.check()` now raises a clear
   `ValueError` up front instead, and the README's `Identity.src` bullet
   states the requirement.

## 8. Lane instruction text (paste into future Grok lane prompts)

> **Emitted-proof performance rules.**  Files you emit are compiled by a
> single-threaded Lean job whose cost is dominated by kernel type-checking and
> by Lean/Mathlib linters walking the proof term — NOT by `field_simp` or
> `ring`.  Therefore:
> (1) Put these nine lines directly after the `namespace` line of every file
> you generate: `set_option linter.unusedVariables false`,
> `linter.unusedSimpArgs`, `linter.unusedSectionVars`, `linter.unusedTactic`,
> `linter.unreachableTactic`, `linter.unnecessarySeqFocus`, `linter.flexible`,
> `linter.style.haveILetI`, `linter.unnecessarySimpa` (all `false`).
> (2) Never write `field_simp` on a goal containing expanded polynomials.  If
> your identity has the shape `scale · h^p · f(X_1,…,X_m) = target` with
> `X_i = n_i/(d_i h^{e_i})`, have the CAS give you the cleared polynomial
> `g(h, n_1,…,n_m) = scale · h^p · f(n_i/(d_i h^{e_i}))`, emit it as a `def`,
> prove `scale * h^p * f (n_1/(d_1*h^{e_1})) … = g h n_1 … n_m` by
> `simp only [defs]; field_simp; ring` (that `field_simp` sees only the m+1
> atoms and is cheap), and finish the real goal with
> `rw [h_1, …, h_m, that_lemma h hh]; simp only [g]; ring`.
> (3) **Only if `g` has more than ~1000 monomials once expanded**, split it
> into blocks of about ten monomials.  Emit one **module** per block:
> `def gBlkNN`, the CAS-computed `def gBlkNNExp` in the source variables, and
> `theorem gBlkNN_eq : gBlkNN h n_1 … = gBlkNNExp … := by simp only [gBlkNN,
> gBlkNNExp]; ring`.  Then an aggregator module importing all blocks whose
> proof is `simp only [g]; rw [gBlk00_eq, gBlk01_eq, …]`.  Do NOT put all
> blocks in one module: the verifier compiles one file per invocation, so
> separate block modules are what buys parallelism, and the content-keyed
> olean cache then makes a one-block edit recompile one block plus the
> aggregator, not everything.  **Below ~1000 monomials, skip this step
> entirely and stop at (2)** — measured on a 68/252-monomial identity,
> splitting cost 20.0 minutes end-to-end against 4.72 minutes unsplit, and a
> single-block edit still cost 4.64 minutes to re-verify (the aggregator's own
> `ring` over the full identity dominates either way, so splitting doesn't
> even win on incremental edits at this size).
> (4) Never use `native_decide`, `decide := true`, `Lean.ofReduceBool`, or
> anything else that adds an axiom.  Axioms must stay exactly `propext`,
> `Classical.choice`, `Quot.sound` — that is the complete list Palomar
> permits, so `native_decide` is categorically forbidden regardless of how
> much faster it would compile.  Put `#print axioms <final theorem>` at the
> end of the aggregator module and **read its output**: a `grind`-style
> tactic can leave the goal open and let Lean insert a silent `sorry` while
> the build still reports `BUILD_EXIT=0` — only `#print axioms` catches that
> (`sorryAx` in the list means the "proof" is fake).
> (5) `maxHeartbeats` does not need raising beyond what already compiles;
> heartbeats bound elaboration, which is not the bottleneck.
> (6) Don't hand-write any of this: `~/lean/tools/lean-speed/emit/lean_speed.py`
> emits (1)-(4) mechanically from a CAS-produced spec (named identities,
> atoms, denominators to clear) — write the spec, run the CLI, compile the
> aggregator once. See its `README.md`.

