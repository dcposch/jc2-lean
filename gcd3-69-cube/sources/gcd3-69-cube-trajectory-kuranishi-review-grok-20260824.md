# Hostile different-model review — GCD3 `(6,9)` cube-core trajectory closure

| Field | Value |
|---|---|
| Claim under review | Frozen cube-core trajectory gate: conditional on the confirmed polynomial cube-core Faber--Laurent landing, both finite-pole alternatives `s in k*` and `s=C(x-a)^m`, `m>=2`, are empty, separately for `d!=0` and the `d=0` polynomial cube core; mixed `(rho3,rho4)` and unmixed two-sheet fibres reconstruct and fail; no arbitrary `(6,9)`, Keller pair, or JC2 inference |
| Overall verdict | **CONFIRMED** |
| Smallest failing identity | none |
| Smallest missing hypothesis | none that breaks a numbered claim (non-blocking: producer length eight is over the degree-six field `Q(q)`, equivalently `Q`-length `48`; high-constant numerators match independently cleared rows only up to nonzero rational integers, as the producer already states) |
| Evidence tier | independent reverse-order integration of the five Laurent potentials from a finite-binomial `W=(1+U)^{1/6}`; hand Euler weights; independent `I=6r` identification at `kappa=0`; actual Faber substitution for `(2.14)`; independent first-row loads and lex Groebner supports on both `(u,v)` charts; second-engine Singular `lp` eliminations, unit certificates, mixed-fibre equality, and `kappa=0` primary decomposition; independent rank-zero, double-root normal, and Weierstrass smoothness checks; unmodified registered replays as regression only |
| Reviewer / model | Grok 4.6 (xAI). Different model family from the producer (OpenAI Codex/Sol). Same reviewer as the cube-mismatch, target-translation, and lower-Pfaffian reviews this successor consumes |
| Repo | `/Users/dc/code/math/jc2` |
| Git HEAD | `c327bdc8d02472feba42573760325099f34b8cdf` (matches the charged basis) |
| Review window (UTC) | 2026-08-24T16:37:55Z – 2026-08-24T16:48:09Z |
| Python | uv-pinned CPython 3.11.11 + SymPy `1.14.0` (registered replay and independent reconstruction) |
| Singular | `/opt/homebrew/bin/Singular` 4.4.1 |
| Host | `dc-mbp-m2.local`, Darwin arm64 |

Producer, freeze, cube-mismatch producer/review, target-translation erratum/review, and the lower-Pfaffian producer/review (universal fibre only) reread in full before any verdict. Do not defer to producer assertions.

- `xmodel/gcd3-69-cube-trajectory-kuranishi-20260824.md` (SHA-256 `069f6280332b44d93dcad17801dc7136d4a79fb06ace101c2dce8a4e746b5e7b`)
- `cases/gcd3_69_cube_trajectory_kuranishi_20260824/REGISTRATION.md` (SHA-256 `7e629e46167d445d74cbdeb3ffbc4f76b26a214c504f938fb1bdf74fac66f557`)
- `cases/gcd3_69_cube_trajectory_kuranishi_20260824/replay.py` (SHA-256 `db14f5a43462317143afa0ec3a56d5fcccb23fe94f5f2f701b14996b06675766`)
- `cases/gcd3_69_cube_trajectory_kuranishi_20260824/verify_kuranishi.sing` (SHA-256 `f6e56bc185c780e3af445fa0de6ea7d23972981a8228ea9fc20b22a2a8ba0c78`)
- `cases/gcd3_69_cube_trajectory_kuranishi_20260824/MANIFEST.sha256` (SHA-256 `6391c23c79dac869a0a11442e5df2dfda496b51602e8796442c31e22721bb766`)
- `cases/gcd3_69_cube_trajectory_kuranishi_20260824/FREEZE.sha256` (SHA-256 `5637ac20df1302f0b8817788c6c88f85429cabbfe3edac2150fd8abddb4d241b`)
- `xmodel/gcd3-69-cube-mismatch-gate-20260824.md` (SHA-256 `6a2799dfe46828c70462d51a842a3fc0adf0515b8ded7a576cdb837d81847d20`)
- `xmodel/gcd3-69-cube-mismatch-review-grok-20260824.md` (SHA-256 `2648eef3b8091970655a94743c6c181343a94534b6454f43c579b310331ba7d7`)
- `xmodel/gcd3-69-target-translation-erratum-20260824.md` (SHA-256 `43fa36968bb90414748330c1b4a5d5169a0eaa21b1925623764e96204e049c78`)
- `xmodel/gcd3-69-target-translation-erratum-review-grok-20260824.md` (SHA-256 `f4cb57ca765138ed2decab01b12a7f884c37f9a847d80e90162ee751bb3df837`)
- `xmodel/gcd3-69-lower-pfaffian-successor-20260824.md` (SHA-256 `7671785519bf4e55b602f117740bd8d8571c6982a8916235407a2bb0a2263043`)
- `xmodel/gcd3-69-lower-pfaffian-successor-review-grok-20260824.md` (SHA-256 `a000619d8b5597add21716d525856c459ff57d5a2b2ab75b85de5d9d08970b27`)
- `cases/gcd3_69_lower_pfaffian_successor_20260824/verify_lower_invariants.sing` (SHA-256 `557f3b33108dfc3279ad7699b796ea8a29eef673d3d162f144f6e655071391e6`)

The committed basis is exactly `c327bdc8d02472feba42573760325099f34b8cdf`. Named producer artifacts remain uncommitted on top of that basis. No producer, case, canonical, ladder, notes, prompt, log, run, or erratum file was edited. No enumerator, exponent rectangle, or AWS helper was written into the tree. Independent reconstruction lived only in `/tmp`.

The cube-mismatch gate is consumed only for the Faber form, the five-row Laurent equivalence, the legal target quotients, and the dichotomy `s in k*` or `s=C(x-a)^m`, `m>=2`. The erratum is consumed only for legality of `P |-> P+q`. The lower-Pfaffian successor is consumed only for the universal reduced decomposition of `I4=I3=I1=0`, `I2=mu` over `Q[a0,...,a4,kappa,mu]`, specialised at `kappa=0`. Nontrivial-Kummer weight vanishing and Kummer descent `X=s R` are not imported. The producer does not import them either.

---

## Promotion

**Accept `CONDITIONAL ON THE CONFIRMED CUBE-CORE FABER--LAURENT REDUCTION, BOTH TERMINAL FINITE-POLE BRANCHES ARE EMPTY. THIS CLOSES d!=0 AND THE SEPARATE d=0 POLYNOMIAL CUBE CORE. IT DOES NOT BY ITSELF CLOSE AN ARBITRARY (6,9) PAIR OR JC2` at the stated scopes.**

- The theorem starts after the reviewed cube-core landing `h=s^3`, `s in k[x]`, `z=sy+r`, `g=[H(f^{1/6})]_+`, `r1'=r2'=r3'=r4'=0`, `6 r5'=j/s`, with both original Taylor jets polynomial. It treats `s in k*` and `s=C(x-a)^m`, `m>=2` separately, and treats `d!=0` and `d=0` separately, retaining every legal target constant of the confirmed quotient.
- Weighted leading components of `r1^0=...=r4^0=0` are exactly the common-cubic surface and one DS curve. Uniform pole laws are `(14-k)p=1` and `(14-k)p=m-1`. The unique double-root projective normal is `(X:Y:Z)=(1:1:-2)` at `(u,v)=(-3,2)`, with cubic `r3=-1/16` independent of the next five coefficients. Rank-zero `(X,Y,Z)=(0,0,0)` is empty on every forced first row. The triple origin is not a weighted-projective pole point.
- For `d!=0` the two orbits `q=u^3/v^2=(45+-3 sqrt(195))/2` are squarefree, the normal fibre has length eight over `Q(q)`, and both `Res(K,phi)` and the full terminal `T_d` are units. Both finite-pole branches fail, by non-integral degree `2/13` and by the original-boundary split of orders `<=1` versus `3/2`.
- For `d=0` the first-nonzero rows of `c7,c5,c4,c2,c1` have the displayed projective supports, all squarefree, with `Res` and `T_theta` units. Constant-`s` degrees are non-integral; monomial cores fail the same strict boundary inequalities for `k<=8`.
- Target loads force `rho1=rho2=0` without setting a later `rho4` to zero after `rho3!=0`. Remaining parameters are `mu=6 rho3`, `nu=6 rho4`. The split `nu!=0` versus `nu=0` is exhaustive.
- On `nu!=0`, `A=0` is lost: it forces `B=0` and then `nu=0`. The localized model is reversible, the curve `72 V^2-3 A^3-512 mu=0` is a smooth plane cubic of genus one for `mu!=0`, and a rational coefficient path supplies a morphism `P^1 -> E` which Riemann--Hurwitz forces constant, hence `r5` constant. For `mu=0` the cusp has rational normalisation `A=24 lambda^2`, `V=24 lambda^3` and `r5=(27/2) lambda^7 - nu^2/(1458 lambda^6)`, whose two distinct pole places are incompatible with either one-pole terminal form. This includes `rho3=0`, `rho4!=0`.
- On `nu=0` the independently reviewed two-sheet decomposition at `kappa=0` applies as universal algebra, not as Kummer descent. Zero-bracket has vanishing source bracket; the elliptic sheet is genus one in `k(x)` and constant; the cusp/DS fibre is a seventh power, then excluded by the DS resultant `(2.10)`. Every surviving rational pole traces back through the original Faber coefficients and `P_0=f(r)`, `Q_0=g(r)`.

**Do not promote this to:** emptiness of an arbitrary `(6,9)` pair; full partial-`y` coverage; a polynomial Keller pair; a JC2 decision; or a silent import of aligned nontrivial-Kummer weight vanishing. Those require the separately reviewed noncube/aligned branch, the first common-cubic landing split, and the surrounding bounded-degree reduction.

**Smallest valid successor.** Consume the reviewed noncube/aligned branch and the first common-cubic landing split, each at its own reviewed scope, if a statement about every `(6,9)` pair is desired. Do not open a generic coefficient rectangle or AWS. Do not relaunch the polynomial cube-core finite-pole analysis.

---

## Quarantine

No result here proves or disproves JC2, constructs or excludes a characteristic-zero Keller pair of type `(6,9)`, or closes arbitrary `(6,9)` independently of the noncube/aligned landing. Producer strings `PASS-GCD3-69-CUBE-TRAJECTORY-SYMBOLICS`, `PASS-GCD3-69-CUBE-KURANISHI-ELIMINATION`, `PASS-GCD3-69-D-EXCEPTIONAL-RECONSTRUCTION`, `PASS-GCD3-69-MIXED-TARGET-FIBER`, and `PASS-GCD3-69-LOWER-INVARIANT-DECOMPOSITION` were not used as evidence; the weights, quadrics, first-row supports, exceptional orbits, original-boundary valuations, mixed elliptic/cusp model, and unmixed two-sheet specialisation were re-derived. The cube-mismatch predecessor is used only for the Faber--Laurent landing and the two-core dichotomy. The erratum is used only for legality of `P |-> P+q`. The lower-Pfaffian successor is used only for the universal reduced primes `P_A`, `P_B` of the four-invariant ideal, at `kappa=0`. Independent reconstruction, not the producer scripts, is the evidence for every numbered claim.

---

## Scope (not enlarged)

Exact identities and a conditional exclusion of both finite-pole alternatives inside the polynomial cube core `h=s^3`, `s in k[x]`, separately for `d!=0` and `d=0`, retaining every legal target constant and both original polynomial boundary values. Arbitrary `(6,9)`, aligned nontrivial Kummer, partial-`y` coverage, a Keller pair, and JC2 remain out of scope.

---

## Headline and subclaim table

| # | Exact subclaim | Verdict | What would have flipped it |
|---|---|---|---|
| 1 | Theorem starts only after the reviewed cube-core Faber--Laurent landing; `s in k*` and `s=C(x-a)^m`, `m>=2` are separate; `d!=0` and `d=0` are separate; all legal target constants and both original polynomial boundary values are retained; no nontrivial-Kummer weight or descent is imported. The proposed weighted cover omits no ramified, rank-zero, component-crossing, zero-load, or infinity stratum that could carry a rational pole | **CONFIRMED** | a hidden Kummer vanishing of `c7,c5,c4,c2,c1`; `d=0` folded into mismatch; only `f(r)` retained; a rank-zero projective solution of a forced first row; a third weighted-projective leading component; an `h=epsilon^{k/n}` bypass of the quadratic/cubic rows |
| 2 | Weights `wt(a_i)=(6-i)`, `wt(d,c7,c5,c4,c3,c2,c1)=(1,2,4,5,6,7,8)`, `wt(r_n)=9+n`. Leading support of `r1^0=...=r4^0=0` is common-cubic union DS. Uniform laws `(14-k)p=1` and `(14-k)p=m-1` with `gamma != 0`. Unique double-root normal, cubic `r3=-1/16`. DS resultant `(2.10)` and common reconstruction `(2.14)` hold. Necessary initial ideals are reconstructed or explicitly retained | **CONFIRMED** | a non-quasihomogeneous `r_n`; a third reduced leading prime; `T_theta=0` on a displayed orbit; a second projective double-root normal cancelling `r3`; Faber `g` differing from `K^3+(3/2)h K phi` at order `<2`; a projection ideal strictly larger than the displayed support |
| 3 | `P_d=2u^6-90 u^3 v^2+135 v^4`, orbits `q=(45+-3 sqrt(195))/2`, both squarefree, length-eight normal fibre, `Res` and `T_d` units, axes force the non-projective origin. Both finite-pole branches empty | **CONFIRMED** | a third `q`-orbit; `4q+27=0`; fibre length not eight over `Q(q)`; a common root of `K` and `phi` on the fibre; `T_d` vanishing; a polynomial degree `2/13` or a boundary cancellation past order `3/2` |
| 4 | First-nonzero supports of `c7,c5,c4,c2,c1` are exactly the displayed ones, squarefree, with `Res` and `T_theta` units on both charts. Constant-`s` degrees non-integral; monomial cores fail `12/k>1` and `18/k>3/2`. All-high-constants-zero is the separate target analysis | **CONFIRMED** | an extra projective orbit; a displayed orbit with `Delta=0`; a unit failure of `Res` or `T_theta`; an integral pair `(2p,3p)` on a nonzero support; `k=8` meeting the boundary threshold |
| 5 | `rho1` support `v=0`, `rho2` support `u=0`, both with `Res` and `Q5` units; `rho3` dominant; `rho4`-first common quadratic empty. Later `rho4` is not set to zero after `rho3!=0`. Parameters `mu=6 rho3`, `nu=6 rho4`; the split `nu=0` vs `nu!=0` is exhaustive | **CONFIRMED** | `rho1` or `rho2` admitting an integral constant-`s` degree after normal corrections; `Ir4` not unit; `I=6r` failing at `kappa=0`; a residual target constant besides `rho3,rho4` |
| 6 | `nu!=0 => A!=0`. Reversible localisation yields `72 V^2-3 A^3-512 mu=0`, `A^2 B=-256 nu/9`, `r5=A^2 V/1024-256 nu^2/(27 A^3)`. For `mu!=0` the plane cubic is smooth of genus one and a rational path from `P^1` is constant. For `mu=0` the displayed normalisation, two-term `r5`, two distinct poles, and incompatibility with each one-pole terminal form all hold, including `rho3=0`, `rho4!=0` | **CONFIRMED** | an `A=0` solution with `nu!=0`; one-sided ideal containment; a singular point of `72 V^2-3 A^3-512 mu=0` at `mu!=0`; a nonconstant morphism `P^1 -> E`; cancellation of either cusp pole of `r5`; a one-pole rational `lambda` |
| 7 | Unmixed `nu=0` is the reviewed two-sheet fibre at `kappa=0`: zero-bracket has `D=0`; elliptic sheet is genus one in `k(x)` and constant; `mu=0` is zero-bracket or DS, excluded by seventh-power plus `(2.10)`. Strongest licensed conclusion is exactly the producer’s cube-core emptiness, not arbitrary `(6,9)`, partial-`y`, a Keller pair, or JC2 | **CONFIRMED** | a third reduced prime at `kappa=0`; nonzero zero-bracket bracket; `X,Y` forced into a cubic Kummer extension; a rational seventh root of an affine function; a hidden `(6,9)` or JC2 sentence |

All remarks below are non-blocking unless marked otherwise. None changes a numbered verdict.

---

## Replay and hashes

Frozen hashes, recomputed on the charged tree, match the launch prompt, `MANIFEST.sha256`, and `FREEZE.sha256`:

| Artifact | SHA-256 | Match |
|---|---|---|
| `xmodel/gcd3-69-cube-trajectory-kuranishi-20260824.md` | `069f6280332b44d93dcad17801dc7136d4a79fb06ace101c2dce8a4e746b5e7b` | prompt, `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_cube_trajectory_kuranishi_20260824/REGISTRATION.md` | `7e629e46167d445d74cbdeb3ffbc4f76b26a214c504f938fb1bdf74fac66f557` | prompt, `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_cube_trajectory_kuranishi_20260824/replay.py` | `db14f5a43462317143afa0ec3a56d5fcccb23fe94f5f2f701b14996b06675766` | prompt, `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_cube_trajectory_kuranishi_20260824/verify_kuranishi.sing` | `f6e56bc185c780e3af445fa0de6ea7d23972981a8228ea9fc20b22a2a8ba0c78` | prompt, `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_cube_trajectory_kuranishi_20260824/MANIFEST.sha256` | `6391c23c79dac869a0a11442e5df2dfda496b51602e8796442c31e22721bb766` | prompt (self-hash), `FREEZE` |
| `cases/gcd3_69_cube_trajectory_kuranishi_20260824/FREEZE.sha256` | `5637ac20df1302f0b8817788c6c88f85429cabbfe3edac2150fd8abddb4d241b` | prompt (self-hash) |
| `xmodel/gcd3-69-cube-mismatch-gate-20260824.md` | `6a2799dfe46828c70462d51a842a3fc0adf0515b8ded7a576cdb837d81847d20` | registration |
| `xmodel/gcd3-69-cube-mismatch-review-grok-20260824.md` | `2648eef3b8091970655a94743c6c181343a94534b6454f43c579b310331ba7d7` | registration |
| `xmodel/gcd3-69-target-translation-erratum-20260824.md` | `43fa36968bb90414748330c1b4a5d5169a0eaa21b1925623764e96204e049c78` | registration |
| `xmodel/gcd3-69-target-translation-erratum-review-grok-20260824.md` | `f4cb57ca765138ed2decab01b12a7f884c37f9a847d80e90162ee751bb3df837` | registration |
| `xmodel/gcd3-69-lower-pfaffian-successor-20260824.md` | `7671785519bf4e55b602f117740bd8d8571c6982a8916235407a2bb0a2263043` | registration |
| `xmodel/gcd3-69-lower-pfaffian-successor-review-grok-20260824.md` | `a000619d8b5597add21716d525856c459ff57d5a2b2ab75b85de5d9d08970b27` | registration |
| `cases/gcd3_69_lower_pfaffian_successor_20260824/verify_lower_invariants.sing` | `557f3b33108dfc3279ad7699b796ea8a29eef673d3d162f144f6e655071391e6` | registration |

The case directory contains exactly those five files (`REGISTRATION.md`, `replay.py`, `verify_kuranishi.sing`, `MANIFEST.sha256`, `FREEZE.sha256`). No enumerator, exponent rectangle, or AWS helper is present.

Registered commands, rerun unmodified from the repository root:

```sh
uv run --offline --no-project --with sympy==1.14.0 python \
  cases/gcd3_69_cube_trajectory_kuranishi_20260824/replay.py

Singular -q \
  cases/gcd3_69_cube_trajectory_kuranishi_20260824/verify_kuranishi.sing

Singular -q \
  cases/gcd3_69_lower_pfaffian_successor_20260824/verify_lower_invariants.sing
```

All three exit 0. Exact output:

```text
PASS-GCD3-69-CUBE-TRAJECTORY-SYMBOLICS
weights=r_n:9+n
leading_components=COMMON-CUBIC-OR-DS
double_normal_cubic_r3=-1/16
pole_balance=constant:(14-k)p=1,monomial:(14-k)p=m-1
exhaustive_load_weights=d:1,c7:2,c5:4,c4:5,c2:7,c1:8,rho1:10,rho2:11,rho3:12,rho4:13
mixed_rho3_rho4=ELLIPTIC-OR-TWO-POLE-CUSP
source_reconstruction=FABER-FIRST-SPLIT,ZERO-BRACKET,DS
aligned_kummer_assumptions_imported=false
```

```text
PASS-GCD3-69-CUBE-KURANISHI-ELIMINATION
d_exceptional=2u6-90u3v2+135v4
d_zero_high_table=c7,c5,c4,c2,c1
all_exceptional_high_orbits=SQUAREFREE-AND-RES-NONZERO-FULL-TERMINAL-NONZERO
zero_high_target_support=rho1:v0,rho2:u0,rho3:dominant,rho4:first-common-empty
PASS-GCD3-69-D-EXCEPTIONAL-RECONSTRUCTION
d_exceptional_normal_fiber_length=8
PASS-GCD3-69-MIXED-TARGET-FIBER
mixed_target_curve=72V2-3A3-512mu
mixed_target_localization=A-NONZERO-FOR-nu-NONZERO
```

```text
PASS-GCD3-69-LOWER-INVARIANT-DECOMPOSITION
minimal_reduced_components=ZERO-BRACKET-SHEET,ELLIPTIC-SHEET
embedded_C_zero_component=CONTAINED-IN-ZERO-BRACKET-SHEET
special_C_zero=ZERO-BRACKET-OR-SHIFTED-DS
```

Those PASS strings are regression only. The independent reconstruction of Claims 1–7 is the evidence. In particular the registered Python replay and this review use opposite integration orders on `(a0,...,a4)` and opposite constructions of `W` (finite binomial versus `sympy.series`); the five potentials coincide, with monomial counts `(31,36,48,55,69)`. Independent Singular certificates used lexicographic order in place of the producer’s `dp(4),dp(2)`.

---

## Claim 1 — scope and exhaustion perimeter

**CONFIRMED.**

The predecessor, independently reviewed, supplies the cube-core identities `h=s^3` with `s in k[x]`, depression `z=sy+r` in `k(x)[y]`, the Faber form with nine constants before quotient, the legal gauges `Q |-> Q-c6 P`, `Q |-> Q-c0`, and `P |-> P+q`, and the five-row equivalence `r1'=...=r4'=0`, `6 r5'=j/s`. Rational exactness of `dx/s` for polynomial `s` forces `s in k*` or `s=C(x-a)^m`, `m>=2`. This successor starts there and nowhere earlier.

The `d!=0` quotient is the confirmed slice `c2=0` with invariants `8d c3-9c2` and `8d c1-7 c7 c2`. The `d=0` quotient is `c3=0` via `q=2 c3/3`, retaining `c7,c5,c4,c2` and `bar(c1)=nu0/9` with `nu0=9 c1-7 c7 c3`. No identity divides by `d` on the `d=0` stratum. Translation changes `a0` by a constant and does not move poles, degrees, or the jets `(2.4)`.

Both original values are retained as `P_0=L^6 Fbar(t,R)` and `Q_0=L^9 Gbar(t,R)`. A failed value row cannot be restored by a deeper Taylor jet. The jets are not set to zero.

No Kummer weight is applied to `c7,c5,c4,c2,c1`. The identity `(I4,I3,I2,I1)=6(r1,r2,r3,r4)` is a polynomial identity at `kappa=0`, obtained by comparing independently integrated potentials with the frozen lower-Pfaffian formulae; it is not a descent statement. The two-sheet decomposition is used only after `nu=0` forces the universal ideal `I4=I3=I1=0`, `I2=mu`.

Weighted cover. Constants of weight `q` enter at `epsilon^q`. When `d!=0`, weight one is strictly first. When `d=0`, the retained high weights are the distinct values `2,4,5,7,8` (`c3` has been gauged away). After those vanish, the target weights are the distinct values `10,11,12,13`. There is no equal-weight collision.

Ramified double-root: all five invariants have vanishing linear term in `h`. The unforced quadrics, saturated away from `X=Y=Z=0` in each of the charts `X!=0`, `Y!=0`, `Z!=0`, and `X+Y+Z!=0`, project onto `Delta=4u^3+27v^2`. Squarefree `K` therefore has no projective first normal. Any earlier `h=epsilon^{k/n}` with `n>2` still meets the quadratic row first; that row forces the unique double-root normal, whose cubic `r3=-1/16` cannot be cancelled by a high constant (every `partial r3 / partial theta` vanishes on the common surface, so a load of order `h^3` still contributes `O(h^4)` to `r3`). A putative `rho3` load at `h^3` can cancel `r3` but then `r1=r2=0` forces `S=0` and `r4=-3/16` remains.

Rank-zero. Independently, the linear loads of `d,c7,c5,c4,c2,c1` on the common surface, evaluated at `X=Y=Z=0`, have no projective zero in `(u,v)`. Target loads at the origin are the unforced quadrics plus a unit, hence nonzero. Zero-load paths that remain on the common surface have `r5^0=0` identically, so cannot satisfy `6 r5'=j/s`.

Component-crossing at the triple origin makes every leading `A_i` zero, so the maximal pole scale was not chosen; rechoosing returns DS or common. Axis points of weighted `P(6,5,4,3,2)` other than that origin do not annihilate `(r1^0,...,r4^0)`:

```text
(a0,...,a4)=(1,0,0,0,0): r3=3/8
(0,1,0,0,0): r1=3/8
(0,0,1,0,0): r3=-1/16
(0,0,0,1,0): r3=3/128
(0,0,0,0,1): r1=-3/256, r3=5/1024.
```

Infinity. For constant `s`, `(2.4)` makes `r` polynomial and the inverse Taylor reconstruction makes every `a_i` polynomial, so the only possible pole is at `x=infinity`. For a monomial core the unique finite pole of `r5` is at `t=0`, so some `a_i` poles there; exclusion at that place kills the path whether or not infinity is also polar.

No omitted stratum carries a rational pole.

---

## Claim 2 — weighted balances and terminal exponents

**CONFIRMED.**

Finite-binomial `W=(1+U)^{1/6}` and reverse-order integration of the five inverted row forms recover potentials homogeneous of weights `10,11,12,13,14`. Euler scaling by `wt(a0,...,a4,d,c7,c5,c4,c3,c2,c1)=(6,5,4,3,2,1,2,4,5,6,7,8)` therefore gives `wt(r_n)=9+n`. The lower-row matrix of `A1,...,A5` against `z^4,...,z^0` is triangular with determinant `6^5`, so the leading four equations `r1^0=...=r4^0=0` are equivalent to the leading Keller rows.

Those four equations at vanishing high constants are the specialisation `I4=I3=I2=I1=0` of the universal invariant ideal, because independently `I_j=6 r_j` at `kappa=0`. The reduced support of that ideal at `mu=0` is the common surface `A=B=w=0` union the DS curve. This is the identification with the confirmed constant-`W` scheme, now as a polynomial identity rather than a citation.

On DS, `r5^0=(27/2) lambda^7 != 0` for `lambda != 0`, so `k=0` and `(14-k)p=14p`. Constant `s` forces `p=1/14` and `deg(a4)=2p=1/7`, impossible. Monomial cores force `14p=m-1`; integrality of `2p` gives `m=7 ell+1`. Actual Faber substitution at `lambda=1` yields

```text
g_DS = z^9+6 z^7+21 z^5+35 z^3+(63/2) z,
Res_z(f_DS,g_DS)=3^9 7^2 / 2^5 != 0.
```

No finite `R=r/L` makes both values vanish; `R -> infinity` makes `P_0 ~ r^6` still polar; `R -> 0` has `f_DS(0)=6 != 0`. Lower terms cannot cancel a nonzero leading resultant.

On the common surface every `r_n^0` vanishes, including `r5`. The first transverse jet is `f=K^2+h phi`, and actual Faber `g=F_9` satisfies

```text
g = K^3 + (3/2) h K phi + O(h^2)
```

as polynomials in `z` (constant and linear terms in `h` vanish identically). Linear terms of all five `r_n` in `h` vanish. The independent quadrics `Q1,...,Q5` match `(2.13)`. Resultant `Res_z(K,phi)` matches the producer polynomial `RES`.

Terminal coefficient: if the first nonzero scaled load has weight `k` and the corresponding full `h^2` coefficient `gamma` of `r5` is nonzero, then `r5 = gamma L^{14-k}+lower`. Comparison with affine `r5` at infinity, or with `r5=c+j t^{1-m}/(6C(1-m))` at a monomial pole, gives `(14-k)p=1` and `(14-k)p=m-1`. Nonvanishing of `gamma` is the unit-ideal assertion `T != 0` on each reconstructed orbit, checked independently below. A necessary initial ideal is never promoted by itself: `d` and the high-constant rows have projection equality plus unit certificates; `rho3` is retained as a global fibre; `rho4`-first common is empty; terminal-only `Q5=1` is the unit ideal.

Double-root. At `(u,v)=(-3,2)`, the quadrics in `(X,Y,Z)` have associated primes `(2Y+Z, 2X+Z)` and `(X,Y,Z)`. The first is the line `(X:Y:Z)=(1:1:-2)`; affine charts see a length-two fat point, not a second geometric normal. The cubic jet along this normal with arbitrary next coefficients `p0,...,p4` is exactly `(3.3)`, in particular `r3=-1/16`. The unforced quadratic jet on this normal is identically zero, so the first obstruction really is cubic.

Source-boundary orders `(2.7)` follow from `L=t^{-p}` and `h=L^{-k/2}`: polynomiality of `P_0` and `Q_0` is `ord_h Fbar >= 12/k` and `ord_h Gbar >= 18/k`. If `K(R)` stays nonzero the orders are zero. If `K(R) -> 0` then `Res(K,phi)!=0` makes `phi(R)` a unit, so `ord_h Fbar <= 1` except possibly at `2 q0=1`, where cancellation in `K^2+h phi` leaves

```text
g(R) = K(R) * (1/2) h phi(R) + O(h^2)
```

of exact order `3/2`. The `O(h^2)` of Faber `g` cannot cancel order `3/2`. For every row with `k<=11` one has `12/k>1` and `18/k>3/2`. Equality first occurs at `k=12`, which is why `rho3` is not discarded by this test.

---

## Claim 3 — the `d!=0` exceptional orbits

**CONFIRMED.**

Scale `d=h^2 D` with `D=1`. Independently cleared `h^2` numerators of `r1,r2,r4,r5` match the producer loads

```text
N1 + 320 u^3 v - 960 v^3,
N2 + 64 u^5 - 1440 u^2 v^2,
N4 + 160 u^6 - 5760 u^3 v^2 + 6480 v^4,
N5 + 320 u^5 v - 2880 u^2 v^3,
```

and `r3` has no `d`-load. Lex Groebner elimination in `(X,Y,Z,u)` at `v=1` recovers exactly `2u^6-90 u^3+135`. The same projection, on both charts and in `lp` order, equals `(P_d)` globally. Axes: `u=0` gives `135 v^4=0`, `v=0` gives `2u^6=0`, so the only common zero is the origin (scheme-theoretically a fat point; set-theoretically not projective).

Put `q=u^3/v^2`. Then `P_d=v^4(2q^2-90q+135)`, and

```text
q = (45 +- 3 sqrt(195))/2.
```

Discriminant `7020=36*195`. Neither root equals `-27/4`: `4q+27=0` would force `195=(117/6)^2=(39/2)^2`, hence `780=1521`. Both orbits are therefore squarefree. The minpoly `2q^6-90 q^3+135` is irreducible over `Q` (Singular `factorize` returns a single factor). Over that degree-six field the normal fibre has `vdim=8`; over `Q` the combined scheme has `vdim=48=8*6`. On the entire scheme, `RES` and `T_d` generate the unit ideal, including after adjoining only `Tu-1` or `Tv-1`.

Constant `s`: `k=1` gives `p=1/13`. Both `u` and `v` are nonzero, so `deg(a4)=2/13` is not an integer.

Monomial cores: `h=epsilon^{1/2}` and `k=1<=11`, so the boundary split of Claim 2 applies. The `d` load itself is order `h^2` in `g`, hence does not affect orders `<2`. Both finite-pole branches are empty.

---

## Claim 4 — the `d=0` high-constant strata

**CONFIRMED.**

Linear loads of `c7,c5,c4,c2,c1` on the common surface were recomputed as `partial r / partial theta`. Clearing the same denominators `1944,5832,8,52488,17496` produces numerators equal to the producer’s `I7,I5,I4,I2,I1` and terminals `T7,...,T1` up to nonzero rational integers in `{+-1,+-3,+-9,+-27,+-81,+-243,+-729}`. Elimination ideals are therefore equal. Independent lex Groebner supports:

| `theta` | `k` | `v=1` chart | `u=1` chart | producer support |
|---|---:|---|---|---|
| `c7` | 2 | `u(u^3-6)` | `v(6v^2-1)` | `uv(u^3-6v^2)` |
| `c5` | 4 | `u^3-3` | `v(3v^2-1)` | `v(u^3-3v^2)` |
| `c4` | 5 | `u(u^3-18)` | `18v^2-1` | `u(u^3-18v^2)` |
| `c2` | 7 | `u^3-9` | `(3v-1)(3v+1)` | `u^3-9v^2` |
| `c1` | 8 | `u` | `v` | `uv` |

`lp` elimination equals the same ideals, and `Res` and `T_theta` are units on both `u!=0` and `v!=0`. Each support is coprime to `Delta` on those charts (the origin is again the only scheme-theoretic meeting point with `Delta`, and is not projective). Rank-zero is empty, as in Claim 1.

Constant `s`. The law `(14-k)p=1` gives denominators `12,10,9,7,6`. Nonzero `u` forces `2p in Z`; nonzero `v` forces `3p in Z`. No listed support makes all of its nonzero leading degrees integral. The `c7` mixed orbit has both `2p=1/6` and `3p=1/4`.

Monomial cores: `k<=8<=11`, so `12/k>1` and `18/k>3/2`. The boundary split of Claim 2 applies with `h=epsilon^{k/2}`. The all-high-constants-zero degeneration is not included in these rows; it is the target analysis of Claims 5–7.

---

## Claim 5 — target-load ordering

**CONFIRMED.**

After `(6.1)`, the first possible nonzero target constant `rho_j` has weight `9+j`. Independent lex supports:

- `rho1`: unit at `v=1`, generator `v` at `u=1`, hence `v=0`;
- `rho2`: generator `u` at `v=1`, unit at `u=1`, hence `u=0`;
- `rho3`: `N3-8` projects to `(0)`, dominant in `(u,v)`;
- `rho4`: `N1=N2=N3=N4-52488` is the unit ideal.

On the `rho1` support, `Res` and `N5` are units in the `u!=0` chart (the only projective chart, since `v=0` forces `u!=0`). On `rho2`, the same holds in the `v!=0` chart. Terminal-only `N5-17496` with `N1=...=N4=0` is unit, so no quadratic normal supplies only `r5`.

Constant `s`. The `rho1` row has `p=1/4` and `deg(a4)=1/2`. The `rho2` row has `p=1/3` and leading `u=0`, so `a4` is subleading; the normal corrections to `(a2,a1,a0)` occur at `epsilon^{11/2}` with degrees `(-1/2,-1/6,1/6)`, none integral. Forcing `X=Y=Z=0` contradicts the nonzero `rho2` load.

Monomial cores for `k=10,11` still have `12/k>1` and `18/k>3/2`. Equality starts at `k=12`, so `rho3` is retained. The empty `rho4`-first common row is not used to kill a later `rho4` after a nonzero `rho3`: the mixed fibre of Claim 6 keeps both parameters.

Independently `I4=6 r1`, `I3=6 r2`, `I2=6 r3`, `I1=6 r4` as polynomials at `kappa=0`. Thus `mu=I2=6 rho3` and `nu=I1=6 rho4`. Either `nu=0` or `nu!=0`.

---

## Claim 6 — mixed `rho3/rho4` fibre

**CONFIRMED.**

At `kappa=0` the invariant numerators are

```text
e4 = -A^2 q + 4 A w + 8 B^2,
e3 = -A^2 p - 4 A B q + 8 B w,
```

checked by substituting the invertible change `(7.6)` into the frozen `e4,e3`. If `A=0`, then `e4=8 B^2`, so `r1=0` forces `B=0`, after which `e3=0` automatically. Direct substitution of `A=B=0` into the frozen `I1` yields `I1=0` identically. The mixed equations with `A` adjoined likewise reduce `nu` to `0`. Localisation at `A` therefore loses no point of `nu!=0`.

Solving `e4=e3=0` for `(q,p)` gives `(7.4)` with no branch choice. The remaining two invariants, after the same substitution, are equivalent to

```text
A^2 B = -256 nu / 9,
72 V^2 - 3 A^3 - 512 mu = 0,
```

where `V=w+8 B^2/A` and `mu=6 r3`, `nu=6 r4`. Conversely, `(7.4)`–`(7.6)` reconstruct every `a_i`. Independent reconstruction of `r0` along this inverse yields `r1=r2=0`, `r4=nu/6`, `r3=(24 V^2-A^3)/1024`, and

```text
r5 = A^2 V / 1024 - 256 nu^2 / (27 A^3).
```

The identity `512 mu = 3(24 V^2-A^3)` converts the `r3` formula into the displayed cubic. Singular equality of the two localized ideals holds in the producer’s `dp` order and in the reverse `lp` order `(T,nu,mu,V,w,B,A,p,q)`. All denominators are powers of the unit `A` and rational integers.

For `mu!=0` the affine curve `72 V^2-3 A^3-512 mu=0` is singular only at `A=V=0`, which would force `mu=0`. Its plane projective closure `72 V^2 W-3 A^3-512 mu W^3=0` meets infinity at `[0:1:0]`, where `dF/dW=72 != 0`. Equivalently `V^2=A^3/24+64 mu/9` is Weierstrass `y^2=x^3+a` with `a=64 mu/9 != 0` and discriminant `-432 a^2 != 0`. The curve is therefore a smooth plane cubic of genus one.

A rational coefficient path gives `A,V in k(x)`, hence a rational map from a dense open of `P^1` to this cubic. The target is projective and the source is a smooth curve, so the map extends to a morphism `P^1 -> E`. A nonconstant morphism of degree `d>=1` would give `-2=R` with ramification `R>=0` by Riemann--Hurwitz, which is impossible. The morphism is therefore constant, so `A,V` are constant, so `(7.4)`–`(7.7)` make every `a_i` and `r5` constant, contradicting `6 r5'=j/s`. Affine `A=0` points of `E` are not identically attained because `A` is not the zero function; they are irrelevant to constancy.

For `mu=0`, `V^2=A^3/24`. The rational normalisation is `A=24 lambda^2`, `V=24 lambda^3` with `lambda=V/A` (the sign of `V` follows `lambda`; `lambda |-> -lambda` is the same `P^1`). Direct substitution of the `r5` formula produces

```text
r5 = (27/2) lambda^7 - nu^2 / (1458 lambda^6).
```

The numerator of this rational function in `lambda` has degree `13` and does not vanish at `0`; the denominator has degree `6`. Poles are therefore of order six at `lambda=0` and of order seven at `lambda=infinity`, and they are distinct. A constant `lambda` makes `r5` constant. A nonconstant `lambda in k(x)` is a nonconstant morphism `P^1 -> P^1`, hence surjective, so the pullbacks of `{0}` and `{infinity}` are nonempty and disjoint. The composition therefore has at least two distinct poles on `P^1`.

An affine `r5=alpha x+beta` for constant `s` has its only pole at infinity. The monomial antiderivative `c+j t^{1-m}/(6C(1-m))` has its only pole at `t=0` (at infinity it is holomorphic of value `c`). Neither one-pole form can equal a two-pole function. This includes the subcase `rho3=0`, `rho4!=0`, which is exactly `mu=0`, `nu!=0`.

---

## Claim 7 — unmixed fibre, reconstruction, and logical closure

**CONFIRMED.**

Now `nu=0`. The equations are `I4=I3=I1=0`, `I2=mu` at `kappa=0`. Independent `lp` primary decomposition recovers exactly three associated primes: `P_A=(A,B,9w^2-64 mu)`, `P_B=(a3,a1,EB,48 a0-12 a2 a4+3 a4^3)`, and `P_E=(mu,A,B,12 a0-3 a3^2)` with `P_A subset P_E`. The embedded component contributes no third field-valued branch. This is the reviewed universal decomposition specialised at `kappa=0`, not a Kummer-weight argument.

Zero-bracket. `A=B=0` and `9w^2=64 mu` give `f=K^2+eta`, `g=K^3+(3 eta/2) K` with `eta=w/4 in k`. For every moving `K` and constant `eta`, the source bracket vanishes identically (direct differentiation). The terminal row cannot occur.

Elliptic sheet. Coordinates `X=8 a2-2 a4^2`, `Y=3 a4 X` satisfy `Y^2=3 X^3+4096 mu`. For `mu!=0` this is again Weierstrass of nonzero discriminant, genus one. Cube-core coefficients lie in `k(x)`, so `X,Y in k(x)` with no Kummer factor `s`. The same Riemann--Hurwitz argument as Claim 6 makes the map `P^1 -> E_mu` constant, hence `r5` constant, contradicting `j/s != 0`. Independently, on `P_B` one has `r1=r2=r4=0` as polynomials in `(a2,a4)`.

If `mu=0`, the sheet is zero-bracket or the DS curve `r5=(27/2) lambda^7`. A nonconstant affine function is not a seventh power in `k(x)`: `alpha x+beta` has a simple zero. For a monomial core, `c+k t^{1-m}=(27/2) lambda^7` forces `c=0` (otherwise the left side has simple finite zeros) and `m=7 ell+1`; the surviving formal value is `lambda=A t^{-ell}`. The nonzero DS resultant `(2.10)` then excludes both original polynomial boundaries, as in Claim 2. `lambda=0` is the triple origin, already not projective.

Tracing poles. Every rational pole of a cube-core coefficient path is either at infinity (constant `s`) or at the unique finite root of `s` (monomial core). In both cases the leading form is one of the rows of the table in Section 8 of the producer, and each row has been excluded either by degree, by original boundary values, by a unit terminal coefficient, or by the exact global fibre of Claims 6–7. No analytic local trajectory is promoted: the predecessor’s regular local `d=1` survivor is excluded only after global degree and boundary conditions.

The strongest licensed conclusion is therefore exactly:

> Assume the confirmed polynomial cube-core Faber--Laurent reduction for an actual-degree `(6,9)` Keller pair. Then neither `s in k*` nor `s=C(x-a)^m`, `m>=2`, admits a rational coefficient trajectory satisfying the original polynomial source boundaries. Hence the complete polynomial cube core is empty, separately for `d!=0` and `d=0`.

This does not close an arbitrary `(6,9)` pair, full partial-`y` coverage, a Keller pair, or JC2. Those implications require the separately reviewed noncube/aligned branch, the first common-cubic landing split, and the surrounding bounded-degree reduction, none of which is consumed here.

---

## Non-blocking remarks

- Producer “length eight” is the `vdim` over the irreducible degree-six ring `Q[q]/(2q^6-90 q^3+135)`. The combined scheme over `Q` has length `48`. Both resultant and terminal remain units at that larger level.
- High-constant producer numerators are nonzero rational-integer multiples of the independently cleared rows. Projection ideals and unit certificates are unaffected, and the producer already claims only this.
- The unique double-root projective normal is scheme-theoretically a length-two fat point on affine charts. Geometrically it remains one point `(1:1:-2)`.
- Axes of `P_d` and of each high-constant support meet `Delta` at the origin as a fat point. Squarefreeness is a projective statement, as the producer writes it.

None of these remarks supplies a missing rational pole or a failing identity.
