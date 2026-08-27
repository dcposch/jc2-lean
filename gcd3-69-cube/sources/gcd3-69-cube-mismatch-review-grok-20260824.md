# Hostile different-model review — GCD3 `(6,9)` cube-mismatch gate

| Field | Value |
|---|---|
| Claim under review | Frozen cube-core mismatch gate: every high-row solution has the exact Faber form `g=[H(f^{1/6})]_+` retaining nine constants before target quotient; the five lower rows are equivalent to `r1'=r2'=r3'=r4'=0`, `6 r5'=j/s`; polynomial `s` with rational exactness of `dx/s` forces `s` constant or a single-root power `m>=2`; a regular local formal survivor exists; `d!=0` is not closed |
| Overall verdict | **CONFIRMED** |
| Smallest failing identity | none |
| Smallest missing hypothesis | none that breaks a numbered claim (non-blocking: the displayed common-landing ranks `(0,1)` are the `c_j=0` slice; first-order motion of the constants is not obstructed) |
| Evidence tier | independent chain-rule/Taylor/depression identities; finite-binomial Faber form plus reverse-order triangular integration of all eight high rows; Taylor derivation of `P |-> P+q`; binomial `A_n` and `det=6^5`; series peeling of `H(w)-g` at three specializations matching the five potentials including sign; hand valuation lattice for `dx/s`; unmodified registered replay as regression only |
| Reviewer / model | Grok 4.6 (xAI). Different model family from the producer (OpenAI Codex, GPT-5 family). Same reviewer as the first common-cubic review and the target-translation erratum review on which this successor depends |
| Repo | `/Users/dc/code/math/jc2` |
| Git HEAD | `1e4480c14f2ab9c4145eb6f6c74f0ac348baf76a` (matches the charged basis) |
| Review window (UTC) | 2026-08-24T14:50:47Z – 2026-08-24T15:13:05Z |
| Python | uv-pinned CPython 3.11.11 + SymPy `1.14.0` (registered replay and independent reconstruction) |
| Host | `dc-mbp-m2.local`, Darwin arm64 |

Producer, freeze, first common-cubic producer/review, and target-translation erratum/review reread in full before any verdict. Do not defer to producer assertions.

- `xmodel/gcd3-69-cube-mismatch-gate-20260824.md` (SHA-256 `6a2799dfe46828c70462d51a842a3fc0adf0515b8ded7a576cdb837d81847d20`)
- `cases/gcd3_69_cube_mismatch_gate_20260824/MANIFEST.sha256` (SHA-256 `3bca39faee225aef205b909914ff39594088ab0dcc19ec911466a053e63be5b5`)
- `cases/gcd3_69_cube_mismatch_gate_20260824/FREEZE.sha256` (SHA-256 `48bf4432f17be451291117e5fbc4a1545640f3bbb6aa18cd5fbd9232e4d20684`)
- `xmodel/gcd3-69-common-cubic-first-gate-20260824.md` (SHA-256 `f63bf74fd1013c74645f9f7fe9292db69199572b390b5b19d160c5ed13b373e8`)
- `xmodel/gcd3-69-common-cubic-first-gate-review-grok-20260824.md` (SHA-256 `5416440bc12bb50ecebfdfa520082aa9e88a26069b43deb13bdaabfcd1690503`)
- `xmodel/gcd3-69-target-translation-erratum-20260824.md` (SHA-256 `43fa36968bb90414748330c1b4a5d5169a0eaa21b1925623764e96204e049c78`)
- `xmodel/gcd3-69-target-translation-erratum-review-grok-20260824.md` (SHA-256 `f4cb57ca765138ed2decab01b12a7f884c37f9a847d80e90162ee751bb3df837`)

The committed basis is exactly `1e4480c14f2ab9c4145eb6f6c74f0ac348baf76a`. Named producer, erratum, and case artifacts remain uncommitted on top of that basis. No producer, case, canonical, ladder, notes, prompt, log, or run file was edited. No enumerator, exponent rectangle, or AWS helper was written into the tree. Independent reconstruction lived only in `/tmp`.

The first common-cubic gate is consumed only for the cube-core split `h=s^3` in `k[x]`, the chain rule `J_{(x,y)}=s J_{(x,z)}`, and the boundary provenance. The target-translation erratum is consumed only for legality of `P |-> P+q` in the absence of a first-target-value pin. Nontrivial-Kummer weight vanishing is not imported. The producer does not import it either.

---

## Promotion

**Accept `THE CUBE-CORE HIGH AND LOWER ROWS INTEGRATE EXACTLY TO A FIVE-INVARIANT FABER--LAURENT SYSTEM; THE TERMINAL ROW FORCES THE POLYNOMIAL CUBE ROOT s TO BE CONSTANT OR A SINGLE-ROOT POWER; d!=0 REMAINS LIVE ON AN EXACT ALGEBRAIC-CURVE/ODE/BOUNDARY SURVIVOR; RAMIFIED COMMON STRATA AND THE d=0 CUBE CORE REMAIN OPEN` at the stated scopes.**

- Depression `z=s y+r` with `r=A/6` and `d=-delta/2` is an identity in `k(x)[y]`, not a polynomial source automorphism. The complete jets `s^ell f^{(ell)}(r)/ell!` and their `g` analogues remain the source-polynomiality conditions. The live mismatch branch is `d!=0`; the `d=0` cube core is a separate open stratum; the aligned nontrivial-Kummer branch is not an input.
- The eight high rows `z^{12},...,z^5` have unique solution `g=[H(w)]_+` with all nine constants `d,c7,c6,c5,c4,c3,c2,c1,c0` before quotient. The four omitted `b`-rows are part of that identity. No Kummer weight is set to zero.
- Target shear `Q |-> Q-c6 P` and translation `Q |-> Q-c0` remove `c6,c0`. First-coordinate translation `P |-> P+q` acts by `(3.2)` and is legal: no frozen degree, monicity, source, or target-value pin consumes it. For `d!=0` the invariants are `8d c3-9c2` and `8d c1-7c7 c2`. Division by `d` is not used at `d=0`; `9c1-7c7 c3` is invariant there.
- The remaining Keller equation is equivalent, not a projection, to `r1'=r2'=r3'=r4'=0`, `6 r5'=j/s`. Deeper Laurent terms `n>=6` contribute no nonnegative power of `z`. The sign of the fixed-`w` identity matches the series definition of `r_n`.
- For polynomial nonconstant `s`, rational exactness of `dx/s` forces a single finite root of multiplicity `m>=2`, with the displayed antiderivative of `r5`. Simple roots, degree one, and several distinct roots are impossible. Constants give affine `r5`. The coefficient path is in `k(x)` because the depressed `a_i` are; poles away from the unique root of `s` are controlled by the boundary jets `(1.3)`, not by constancy of `r1,...,r4` alone.
- A regular local formal/analytic trajectory exists through `(a0,...,a4)=(0,0,0,0,1)`, `d=1`, `c_j=0`. Weighted first-order ranks and the DS correction are exact on the displayed `c_j=0` slice. They prove local formal survival and, on that slice, failure of ordinary first-order common landings. Ramified/Puiseux arcs, moving-constant first-order arcs, and polynomiality remain open.

**Do not promote this to:** emptiness of `d!=0`; emptiness of the `d=0` cube core; closure of `(6,9)`; a polynomial Keller pair; or JC2.

**Smallest valid successor.** Four separate bounded gates, not one: (i) rational components of the invariant fibres at constant `s`; (ii) the same at monomial `s=C(x-a)^m`, `m>=2`, with the jets `(1.3)`; (iii) the first nonzero ramified Kuranishi row at squarefree, double, and triple common landings, retaining moving constants; (iv) the `d=0` cube core with quotient `(3.4)`. Do not open a generic coefficient rectangle or AWS. Do not silently fold `d=0` into a claim that “the mismatch branch” is closed.

---

## Quarantine

No result here proves or disproves JC2, constructs or excludes a characteristic-zero Keller pair of type `(6,9)`, closes `d!=0`, closes the `d=0` cube core, or excludes ramified common landings. Producer string `PASS-GCD3-69-CUBE-MISMATCH-GATE` was not used as evidence; the chain rule, Faber form, eight `b`-rows, target-gauge identities, Laurent decomposition, divisor argument, and exact controls were re-derived. The first common-cubic gate is used only for the cube-core split and chain rule at their reviewed scope. The target-translation erratum is used only for legality of `P |-> P+q`. Independent reconstruction, not the producer script, is the evidence for every numbered claim.

---

## Scope (not enlarged)

Exact identities in the polynomial cube core `h=s^3`, `s in k[x]`: high-row Faber form with nine constants, target-translation quotient, five-row Laurent equivalence, finite-pole dichotomy for rational exactness of `dx/s`, and local formal survival. Polynomiality of a coefficient path, the jets `(1.3)`, the `d=0` cube core, ramified common strata, arbitrary `(6,9)`, and JC2 remain out of scope.

---

## Headline and subclaim table

| # | Exact subclaim | Verdict | What would have flipped it |
|---|---|---|---|
| 1 | From cube core `h=s^3`, depression is `z=s y+r` with `r=A/6`, `d=-delta/2`, and `J_{(x,y)}=s J_{(x,z)}`. This is not a polynomial source automorphism. Full jets `(1.3)` are retained. The live branch is `d!=0`; `d=0` is a separate cube-core stratum; aligned nontrivial Kummer is excluded from this gate | **CONFIRMED** | leftover `z_x` in the Jacobian; `z=s y+r` treated as a polynomial source auto; only `f(r),g(r)` retained, or both forced to vanish; Kummer weight vanishing applied to cube-core constants; `d=0` folded into mismatch |
| 2 | All eight high rows, and only those solutions, are `g=[H(w)]_+` with nine constants `d,c7,...,c0` before quotient. The four omitted `b`-rows belong to the identity. No Kummer vanishing is smuggled in | **CONFIRMED** | a high-row remainder for the Faber pair; triangular integration producing a different potential; a pivot other than `-6`; any of `c7,c5,c4,c2,c1` set to zero in the general form |
| 3 | `P |-> P+q` acts by `(3.2)`; `Q |-> Q-c6 P` and `Q |-> Q-c0` remove `c6,c0`. Invariants `8d c3-9c2` and `8d c1-7c7 c2` for `d!=0`; no division by `d` at `d=0`, where `9c1-7c7 c3` is invariant. No retained gauge violates a frozen degree/monicity or value pin | **CONFIRMED** | `g` not invariant under simultaneous `(3.2)`; opposite sign on any `c_j` shift; `mu` or `nu` moving; `q=2c3/3` used while dividing by `d`; a hidden pin of `P(x,0)` or of actual degree |
| 4 | `A1,...,A5` and `det=6^5` hold. `J_{(x,z)}=sum_{n=1}^5 r_n' A_n` as polynomials, hence the remaining Keller equation is equivalent to `r1'=...=r4'=0`, `6 r5'=j/s`. Sign of the fixed-`w` derivative matches the series `H(w)-g`. Terms `n>=6` contribute nothing nonnegative | **CONFIRMED** | `A1` constant term other than `a2-a4^2/12`; `det M != 6^5`; a nonzero polynomial remainder `J-sum r' A`; `A_n` of nonnegative degree for some `n>=6`; series `r5` of opposite sign to the potential |
| 5 | Rational exactness of `dx/s` for polynomial nonconstant `s` forces `s=C(x-a)^m`, `m>=2`, and `(5.4)`. Simple roots, several distinct roots, degree one, and logarithms are impossible. `r5 in k(x)` is licensed. Boundary jets, not the `r`-invariants alone, control extra poles of the coefficient path | **CONFIRMED** | a simple-root rational primitive; `m-1 > m-r` failing to force `r=1`; a degree-one rational antiderivative; `r5` depending on a non-rational coefficient; `(1.3)` treated as redundant once `r_i` are constant |
| 6 | Regular local point, determinant `(6.1)`, and velocity `(6.2)` reconstruct. Frozen-`c` ranks `(6.3)` and DS correction `(6.4)` reconstruct. These prove local formal survival and failure of ordinary first-order arcs on the `c_j=0` slice only. Ramified/Puiseux arcs and polynomiality remain open | **CONFIRMED** | a vanishing five-by-five determinant at the regular point; different `r`-values; DS ranks other than `(4,4)`; promotion of the local trajectory to a rational/polynomial path; a claim that ramified common landings are empty |
| 7 | Strongest licensed conclusion is the Faber–Laurent reduction plus the constant/single-root dichotomy. Not emptiness of `d!=0`, not emptiness of `d=0`, not `(6,9)` exclusion, not a Keller pair, not JC2. Constant-`s`, monomial-`s`, `d=0`, and ramified common strata must be separate successors | **CONFIRMED** | a hidden emptiness of the invariant fibres; `d=0` included in a mismatch closure; a successor that mixes constant-`s` with ramified common landings; a JC2 or `(6,9)` sentence |

All remarks below are non-blocking unless marked otherwise. None changes a numbered verdict.

---

## Replay and hashes

Frozen hashes, recomputed on the charged tree, match the launch prompt, `MANIFEST.sha256`, and `FREEZE.sha256`:

| Artifact | SHA-256 | Match |
|---|---|---|
| `xmodel/gcd3-69-cube-mismatch-gate-20260824.md` | `6a2799dfe46828c70462d51a842a3fc0adf0515b8ded7a576cdb837d81847d20` | prompt, `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_cube_mismatch_gate_20260824/PREREGISTRATION.md` | `acec70acf71b187ec953df9977b23ad04d3df9f0f6582fc37a166b34115be48d` | prompt, `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_cube_mismatch_gate_20260824/replay.py` | `39246c1329c534adce2339ca940962cbb83951d7044b4888a8c7ea04fbd514dd` | prompt, `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_cube_mismatch_gate_20260824/MANIFEST.sha256` | `3bca39faee225aef205b909914ff39594088ab0dcc19ec911466a053e63be5b5` | prompt (self-hash), `FREEZE` |
| `cases/gcd3_69_cube_mismatch_gate_20260824/FREEZE.sha256` | `48bf4432f17be451291117e5fbc4a1545640f3bbb6aa18cd5fbd9232e4d20684` | prompt (self-hash) |
| `xmodel/gcd3-69-common-cubic-first-gate-20260824.md` | `f63bf74fd1013c74645f9f7fe9292db69199572b390b5b19d160c5ed13b373e8` | producer charge, preregistration |
| `xmodel/gcd3-69-common-cubic-first-gate-review-grok-20260824.md` | `5416440bc12bb50ecebfdfa520082aa9e88a26069b43deb13bdaabfcd1690503` | producer charge, preregistration |
| `xmodel/gcd3-69-target-translation-erratum-20260824.md` | `43fa36968bb90414748330c1b4a5d5169a0eaa21b1925623764e96204e049c78` | predecessor freeze |
| `xmodel/gcd3-69-target-translation-erratum-review-grok-20260824.md` | `f4cb57ca765138ed2decab01b12a7f884c37f9a847d80e90162ee751bb3df837` | predecessor review |

The case directory contains exactly those four files. No enumerator, exponent rectangle, or AWS helper is present.

Registered command, rerun unmodified from the repository root:

```sh
uv run --offline --no-project --with sympy==1.14.0 python \
  cases/gcd3_69_cube_mismatch_gate_20260824/replay.py
```

Exit 0. Exact output:

```text
PASS-GCD3-69-CUBE-MISMATCH-GATE
high_row_normal_form=g=[H(f^(1/6))]_+
pinned_constants=d,c7,c6,c5,c4,c3,c2,c1,c0
global_target_gauges=REMOVE-c6,c0-AND-QUOTIENT-P-TRANSLATION
d_nonzero_invariants=8d*c3-9c2,8d*c1-7c7*c2
d_zero_cube_core=OPEN-SEPARATE-STRATUM
lower_rows=r1'=r2'=r3'=r4'=0,6r5'=j/s
cube_core_terminal=s-CONSTANT-OR-SINGLE-ROOT-POWER
regular_local_formal_survivor=true
common_ramified_puiseux_strata=OPEN
cube_mismatch_closed=false
degree_69_closed=false
keller_pair_found=false
jc2_inference=false
```

Those PASS strings are regression only. The independent reconstruction of Claims 1–7 is the evidence. In particular the registered script and this review use opposite integration orders on `(a0,...,a4)` and opposite constructions of `F_j` (finite binomial `W=(1+U)^{1/6}` versus `sympy.series`); the identities coincide.

---

## Claim 1 — source-honest cube-core normalization

**CONFIRMED.**

A genuine actual-degree `(6,9)` pair has, after constant target scalings, `a6=h^2`, `b9=h^3`. In the cube core, Gauss’s lemma puts `h` equal to a constant times a polynomial cube, so `s` may be taken in `k[x]` with `h=s^3`. Write `A=a5/s^5`, `B=b8/s^8`, `delta=3A-2B in k`, `r=A/6`. Independently expanding the truncated polynomials `(z-r)^6+A(z-r)^5` and `(z-r)^9+B(z-r)^8` kills the `z^5` coefficient of `f` and sends the `z^8` coefficient of `g` to `B-9r=B-3A/2=-delta/2`. The producer’s `d=-delta/2` is that coefficient.

The substitution `z=s y+r` is an identity in `k(x)[y]`. It is not a polynomial automorphism of the source plane unless `s in k^*` and `r in k[x]`. Direct expansion with a generic `z_x=s' y+r'` gives

```text
P_x = f_x + f_z z_x,     P_y = s f_z,
Q_x = g_x + g_z z_x,     Q_y = s g_z,
J_{(x,y)} = (f_x+f_z z_x)(s g_z) - (s f_z)(g_x+g_z z_x)
          = s (f_x g_z - f_z g_x).
```

The two `z_x` summands cancel as polynomials. No polynomiality of `r` is used.

Taylor expansion in `y` is the identity

```text
f(r+s y) = sum_{ell=0}^6 (s^ell f^{(ell)}(r)/ell!) y^ell,
```

and likewise for `g`. Source polynomiality of `(P,Q)` is exactly `(1.3)`, all jets, not merely `f(r),g(r)`. Setting those boundary values to zero would make `y` divide both coordinates and hence the Jacobian. The producer retains the full jets and does not set them to zero.

Three strata remain distinct. Nontrivial cubic Kummer forces `delta=0` and the weight vanishings `c7=c5=c4=c2=c1=0`; that branch is the charged first gate plus the lower-Pfaffian successor, and is not rerun here. The cube core has no such Galois action, so those constants survive. Inside the cube core, `d!=0` is the live mismatch branch of this gate; `d=0` is a specialization of the same formulas with a different target quotient, and is left open. No identity failed.

---

## Claim 2 — complete Faber high-row form

**CONFIRMED.**

Let `U=a4 u^2+a3 u^3+a2 u^4+a1 u^5+a0 u^6` and `W=(1+U)^{1/6}` as a polynomial in `u` truncated at degree `9`, computed by the finite binomial sum `sum_k C(1/6,k) U^k` (each `U^k` starts at `u^{2k}`). Set `w=u^{-1} W`. Truncated multiplication gives `W^6` of degree `6`, and the polynomial part of `w^6` is exactly `f`. The polynomial parts `F_j=[w^j]_+` are monic of degree `j`, with `F_0=1`, `F_1=z`, `F_6=f`.

Define `H(T)=T^9+d T^8+c7 T^7+...+c0` and `g=[H(w)]_+`. Direct extraction of `z`-coefficients recovers the four displayed rows `(2.3)` and the four omitted rows

```text
b3 = (3/2) a0 + (4/3) d a1 + (3/4) a2 a4 + (7/6) c7 a2
     + (3/8) a3^2 + (4/9) d a3 a4 + c6 a3
     - (1/16) a4^3 + (7/72) c7 a4^2 + (5/6) c5 a4 + c3,

b2 = (4/3) d a0 + (3/4) a1 a4 + (7/6) c7 a1
     + (3/4) a2 a3 + (4/9) d a2 a4 + c6 a2
     + (2/9) d a3^2 - (3/16) a3 a4^2 + (7/36) c7 a3 a4
     + (5/6) c5 a3 - (4/81) d a4^3 + (2/3) c4 a4 + c2,
```

together with the longer `b1,b0` recorded by the reconstruction (denominators `10368` and `7776`). Specialising `d=c7=c6=c5=c4=c2=c1=0` recovers the first-gate zero-constant `b3=(24 a0+12 a2 a4+6 a3^2-a4^3)/16`. Every one of `d,c7,...,c0` appears; none is set to zero.

Conversely, the eight source rows `z^{12},...,z^5` of `f_x g_z-f_z g_x` are triangular in `(b7',...,b0')` with pivot `-6` at each step (the leading term of `-f_z z^j`). Each row is a closed polynomial one-form on `(a0,...,a4)`. Integrating in the reverse order `a0,a1,a2,a3,a4` from the producer’s `a4`-first order produces eight potentials plus eight constants, and the resulting `g` is identically the Faber polynomial. The Faber pair then kills `z^{12},...,z^5` by direct substitution. Uniqueness of the triangular solution says there are no further high-row solutions.

Because `w^j` is a function of `f`, its full bracket with `f` vanishes. Removing the negative Laurent tail of `w^j` can affect only `z^4,...,z^0`. That is why the eight-parameter family saturates the high rows and why the five lower rows remain.

No identity failed.

---

## Claim 3 — target quotient

**CONFIRMED.**

Shear `g |-> g-c6 f` is `Q |-> Q-c6 P`. Since `[w^6]_+=f`, this subtracts `c6 F_6` and removes `c6`. Translation `g |-> g-c0` removes `c0`. Leading terms remain `z^6` and `z^9`; actual degrees `(6,9)` and monicity are untouched. The cube-core leading identity `a6=s^6`, `b9=s^9` lives in those leading terms and is not moved. Boundary values stay polynomial. Jacobian `1` is preserved.

First-coordinate translation `P |-> P+q` is the residual target automorphism `(u,v) |-> (u+q,v)`. No frozen hypothesis of this gate, of the first common-cubic gate, or of the erratum pins a numerical value of the first target coordinate. Preferring a slice with `c2` visible is not a prohibition. Independently: `w_new=(w^6+q)^{1/6}=w+q/(6 w^5)+O(w^{-11})`. Taylor of `H` has next term of order `O(w^{-3})` in the polynomial part, so

```text
H(w) = H_new(w_new) + q ((3/2) w^3 + (4d/3) w^2 + (7 c7/6) w + c6)
       + (negative Laurent).
```

Matching polynomial parts forces exactly `(3.2)`:

```text
a0 |-> a0+q,
c3 |-> c3-3q/2,     c2 |-> c2-4 d q/3,
c1 |-> c1-7 c7 q/6, c0 |-> c0-c6 q,
```

with `d,c7,c6,c5,c4` fixed. Simultaneous substitution leaves `g` identically unchanged as a polynomial in `z`. Consequently

```text
mu = 8 d c3 - 9 c2,       nu = 8 d c1 - 7 c7 c2
```

are invariant, as are the barred coordinates `(3.3)`. The combination `nu0=9 c1-7 c7 c3` is invariant even without setting `d=0`; the producer only needs it on that stratum, where `c2` is likewise invariant and division by `d` is forbidden. Setting `c2_new=0` uses `q=3 c2/(4d)` and requires `d!=0`. Setting `c3_new=0` uses `q=2 c3/3` and does not.

No retained operation reintroduces a `z^5` or `z^8` term, cancels a leading term, or consumes a source pin. Residual source translations of `z` would reintroduce `z^5` and are not used.

No identity failed.

---

## Claim 4 — five lower rows

**CONFIRMED.**

Write `H(w)-g=sum_{n>=1} r_n w^{-n}`. This starts at `w^{-1}` because `g=[H(w)]_+`. The constants `c6,c0` never appear: `w^6=f` identically, so `c6(w^6-f)+c0-c0=0` even before the shear `(3.1)`. Direct differentiation of the unreduced Faber pair confirms that `c6,c0` drop from every coefficient of `z^4,...,z^0`.

At fixed `w`, `f=w^6` and `g=H(w)-sum r_n w^{-n}`. Then `f_x|_w=0`, `f_w=6 w^5`, `g_x|_w=-sum r_n' w^{-n}`, and

```text
J_{(x,w)} = 6 w^5 sum r_n' w^{-n}.
```

The chain rule `J_{(x,z)}=J_{(x,w)} w_z` together with `f_z=6 w^5 w_z` yields

```text
J_{(x,z)} = f_z sum_{n>=1} r_n' w^{-n}
```

as formal Laurent series at `z=infinity`. The polynomial part of the left side is `J_{(x,z)}` itself. The polynomial part of the right side is `sum r_n' A_n` with `A_n=[f_z w^{-n}]_+`. Independent binomial expansion of `(1+U)^{-n/6}` recovers

```text
A1 = 6z^4 + 3 a4 z^2 + 2 a3 z + a2 - a4^2/12,
A2 = 6z^3 + 2 a4 z + a3,
A3 = 6z^2 + a4,
A4 = 6z,
A5 = 6.
```

Hand collection for `A1`: `w^{-1}=z^{-1}-a4/(6 z^3)-a3/(6 z^4)-a2/(6 z^5)+(7/72) a4^2 z^{-5}+O(z^{-6})`, multiplied by `f_z=6z^5+4 a4 z^3+3 a3 z^2+2 a2 z+a1`, produces constant term `a2-a4^2/12` and no `z^3`. For `n>=6` the leading term of `f_z w^{-n}` is `6 z^{5-n}` with only more negative corrections (`U` starts at `z^{-2}`); the polynomial parts of `n=6,7,8` vanish identically, and higher `n` are strictly worse.

The matrix of `(A1,...,A5)` against `(z^4,...,z^0)` is lower triangular with diagonal `(6,6,6,6,6)`, determinant `6^5`. Invertibility converts the five polynomial identities `J_{z^4}=...=J_{z^1}=0`, `J_{z^0}=j/s` into

```text
r1'=r2'=r3'=r4'=0,     6 r5' = j/s.
```

This is an equivalence of polynomial systems, not a necessary-only projection: `J=sum_{n=1}^5 r_n' A_n` was checked as a polynomial identity after integrating the inverted one-forms. On the locus `r1'=...=r4'=0` the constant row collapses to `6 r5'` because `A5=6`.

The five potentials, integrated `a0`-first, are polynomials of `31,36,48,55,69` monomials in `(a0,...,a4,d,c7,c5,c4,c3,c2,c1)`. Series peeling of `H(w)-g` in powers of `w^{-1}` at three specializations — the regular point, a generic rational point with mixed `c_j`, and the origin — reproduces those potentials including sign. (Order `u^{4}` truncation of `w^9` contaminates only `r5`; order `u^{9+5}` matches.)

No identity failed.

---

## Claim 5 — finite-pole theorem

**CONFIRMED.**  No valuation case was omitted.

In the polynomial cube core the original `y`-coefficients lie in `k[x]`. Depression expresses each `a_i` as a polynomial in those coefficients and in `r=A/6=a5/(6 s^5)`, hence `a_i in k(x)`. Each `r_n` is a polynomial in the `a_i` and the constants, so `r5 in k(x)`. Equation `(4.4)` says that the rational one-form `(j/6) dx/s` is exact.

Let `s` be nonconstant of degree `m`, with `r` distinct finite roots of multiplicities `e_i`. Differentiation in characteristic zero raises every finite pole order of a rational function by exactly one (`d/dx of c (x-a)^{-v}` is `-v c (x-a)^{-v-1}` with `v!=0`). Consequently a rational derivative cannot have a simple pole. A simple root of `s` would give `r5'` a simple pole, which is impossible. Independently, `int dx/x` and `int dx/(C(x-a))` are logarithmic, not rational.

At a root of multiplicity `e_i>=2`, `1/s` has pole order `e_i`, so `r5` has pole order exactly `e_i-1`. No other finite pole of `r5` can exist: a pole of `r5` would produce a pole of `r5'`, and `r5'` poles only at zeros of `s`. The finite pole degree of `r5-c` is therefore `sum_i (e_i-1)=m-r`.

At infinity, for `m>=2`,

```text
1/s = lc(s)^{-1} x^{-m} (1+O(x^{-1})),
```

and integration of the leading term produces

```text
r5-c = j/[6 lc(s)(1-m)] x^{1-m} + lower.
```

The leading coefficient is nonzero (`j!=0`, `m!=1`), so `r5-c` has a zero of exact order `m-1` at infinity and no pole there. A nonzero rational function has equal zero and pole degrees. The function `r5-c` is nonzero because `r5'=j/(6s)!=0`. Hence `m-1 <= m-r`. Combined with `r>=1` (nonconstant polynomial over algebraically closed `k`) this forces `r=1`. Degree `m=1` was already excluded. This is the dichotomy `(5.3)`–`(5.4)`. Direct differentiation checks the monomial antiderivative:

```text
6 d/dt ( j t^{1-m} / (6 C (1-m)) ) = j / (C t^m).
```

Explicit tests, all exact:

| Case | Form | Rational primitive? |
|---|---|---|
| simple root | `dx/x` | no (log) |
| degree one | `dx/(C(x-a))` | no (log) |
| two simple roots | `dx/(x(x-1))` | no (log) |
| double root | `dx/x^2` | yes, `-1/x` |
| triple root | `dx/x^3` | yes, `-1/(2x^2)` |
| two double roots | `dx/(x^2(x-1)^2)` | no: residues `2,-2,0` at `0,1,infty`; integral has `2 log x-2 log(x-1)`. Degree comparison would also forbid it: `m-1=3 > m-r=2` |
| constant `s` | `dx` | yes, affine `r5` |
| infinity, `m>=2` | `x^{-m} dx` | `x^{1-m}/(1-m)` |

The argument is independent of `d` and applies verbatim to the open `d=0` cube core. It does not apply to nontrivial Kummer, where `s` is not in `k(x)`.

When `s` is constant, `(4.4)` makes `r5` affine in `x`. When `s=C(x-a)^m`, polynomiality of `(P,Q)` forces the depressed `a_i` to be Laurent polynomials in `x-a` (poles of the rational depression occur only at zeros of `s`). Constancy of `r1,...,r4` does not by itself forbid extra poles of the `a_i` that cancel in those four polynomials; the jets `(1.3)` do. The producer correctly leaves `(1.3)` to be imposed and does not claim that monomial cores are empty.

No identity failed. No valuation case was omitted.

---

## Claim 6 — controls and exceptional strata

**CONFIRMED.**

Primitive control: `P=(x y)^6`, `Q=(x y)^9+d (x y)^8` is a polynomial cube-core pair with `s=x`, `r=0`, both boundaries polynomial, and all high rows of Faber type `H(T)=T^9+d T^8`. Its Jacobian vanishes identically because both coordinates are functions of `z=x y`. Separately, `dx/x` is not rationally exact, so the terminal theorem already excludes a Keller trajectory with this squarefree core. It is not a Keller pair, and the producer does not treat it as one.

Regular local point: `d=1`, all `c_j=0`, `(a0,a1,a2,a3,a4)=(0,0,0,0,1)`. Two methods (inverted Pfaffian potentials; series peeling of `H(w)-g` at `f=z^6+z^4`) give

```text
(r1,...,r5) = (-3/256, -8/729, 5/1024, 20/6561, -5/6144).
```

The five-by-five matrix of `z^4,...,z^0` rows against `(va0,...,va4)` has determinant `92286875/25048249270272 !=0`. Terminal right-hand side `1` produces velocity

```text
(128/3,
 131072/729,
 194683904/177147,
 1221232033792/4485142125,
 1689034934081536/1089889536375).
```

The inverse-function theorem in the analytic/formal category supplies a unique local trajectory. Nothing promotes it to a rational or polynomial path, and no boundary jet is imposed. The control forbids an algebraic “all rows inconsistent” verdict, and that is all it forbids.

Weighted `d`-deformation, `c_j` frozen at `0`, at the four displayed points:

| Point | `(rank linear, rank augmented)` |
|---|---|
| DS `(6,0,10,0,4)`, `d=0` | `(4,4)` |
| squarefree common `(0,0,1,0,2)` | `(0,1)` |
| double common `(4,-12,9,4,-6)` | `(0,1)` |
| triple origin | `(0,0)` |

These are the producer’s `(6.3)`. With `a4` fixed on the DS slice the unique solution of the four linearized equations is exactly `(6.4)`:

```text
(delta a0, delta a1, delta a2, delta a3, delta a4)
  = (0, -660128/531441, 0, -50176/531441, 0).
```

On the `c_j=0` slice, ordinary first-order `d`-arcs fail at squarefree and double common points (the `d`-load is not in the `a`-image) and are unobstructed along DS. The triple point is exceptional already at first order (`d`-load vanishes). The common residual scheme of the first gate is nonreduced, so a deviation of order `sqrt(d)` can contribute quadratically at the same order; ramified/Puiseux arcs are open, as claimed. Polynomiality is not addressed.

Non-blocking refinement, not a flipped verdict. Enlarging the linearisation to `(a0,...,a4,c7,c5,c4,c3,c2,c1)` at the same points gives

| Point | `rank_a` | `rank_{a,c}` | `rank_{a,d}` | `rank_{a,c,d}` | `d` in `(a,c)`-span |
|---|---:|---:|---:|---:|---|
| DS | 4 | 4 | 4 | 4 | yes |
| squarefree common | 0 | 3 | 1 | 3 | yes |
| double common | 0 | 3 | 1 | 3 | yes |
| triple | 0 | 0 | 0 | 0 | yes (trivially) |

Ordinary first-order motion of the constants is therefore not obstructed on the squarefree and double loci. The producer computed `(6.3)` after the sentence “Setting `c_j=0`” and does not use those ranks to close any landing. The licensed conclusion — local formal survival, ramified/polynomiality open — is unchanged. Successor work that treats common landings must include the constants among the lower-weight data.

No identity failed.

---

## Claim 7 — logical closure

**CONFIRMED.**

The frozen survivor in producer §7 is exactly what the identities license: after target quotient, a `d!=0` candidate is a tuple of constants `(d,c7,c5,c4,mu,nu,rho1,...,rho4)`, a rational path on a component of `r_i=rho_i`, either constant `s` with affine `r5` or a monomial core `(5.3)`–`(5.4)`, and the complete jets `(1.3)` with actual degrees `(6,9)` and inverse-depression provenance. Generically the four invariants cut a curve in five coefficient variables; the regular point shows that at least one fibre is locally a smooth curve with `r5` as a coordinate. That is an algebraic-curve/rational-trajectory problem, not an empty coefficient rectangle.

Attempts to close further, without added hypotheses, fail in every direction.

- Emptiness of `d!=0`. Contradicted by the regular local trajectory. Polynomiality of that trajectory is not proved, so emptiness of polynomial `d!=0` paths is likewise unproved.
- Emptiness of `d=0`. The high-row and Laurent identities specialise polynomially in `d`. The quotient must change to `(3.4)`. The first gate’s Kummer vanishings do not apply. Open, and larger than the aligned branch.
- Full `(6,9)` exclusion. The aligned nontrivial-Kummer branch is a different gate. Cube-core `d!=0` is not closed. Cube-core `d=0` is not closed. Arbitrary `(6,9)` is not in scope.
- A Keller pair. The primitive control has Jacobian zero. The regular trajectory is not shown rational. No pair is exhibited.
- JC2. None of the above is a Jacobian-conjecture decision.

The smallest exact successor therefore splits. Constant-`s` (affine `r5`, polynomial `a_i`, jets `(1.3)`) is one bounded problem. Monomial `s=C(x-a)^m` (Laurent polynomials in `x-a`, prescribed polar `r5`, jets `(1.3)`) is another. The `d=0` cube core with quotient `(3.4)` is a third. Ramified/Puiseux common landings, including moving constants and the triple point, are a fourth. Mixing any two of these into a single emptiness claim would be a silent extra hypothesis. Producer §8 lists the same four gates, in that order, and licenses no generic rectangle and no AWS.

No identity failed.

---

## Non-blocking remarks

1. The combination `9c1-7c7 c3` is invariant under `P |-> P+q` even for `d!=0`. The producer only invokes it on the `d=0` stratum, which is the correct place to use it.
2. The constants `c6,c0` are absent from every Laurent coefficient even before the shear `(3.1)`, because `w^6=f` identically. The producer’s weaker statement that they disappear after `(3.1)` is true.
3. Constant target scalings that would send `d` to `1` move `j` unless `j` is unpinned. The producer retains `d` in every formula and uses `d=1` only as a control point. No identity depends on a normalisation `d=1`.
4. Scheme-theoretic intersection language from the first gate (`P_common+P_DS` of length two) is not re-litigated. It is the reason ramified common landings remain open, and it is used only at that reviewed scope.
5. The phrase “all normalized coefficients have possible finite poles only at `x=a`” is licensed by polynomial source plus unique-root `s`, not by the `r`-invariants alone. The producer immediately adds that `(1.3)` remains. That is the correct division of labour.

---

## Promotion (restated)

**Accept `THE CUBE-CORE HIGH AND LOWER ROWS INTEGRATE EXACTLY TO A FIVE-INVARIANT FABER--LAURENT SYSTEM; THE TERMINAL ROW FORCES THE POLYNOMIAL CUBE ROOT s TO BE CONSTANT OR A SINGLE-ROOT POWER; d!=0 REMAINS LIVE ON AN EXACT ALGEBRAIC-CURVE/ODE/BOUNDARY SURVIVOR; RAMIFIED COMMON STRATA AND THE d=0 CUBE CORE REMAIN OPEN` at the stated scopes.**

**Do not promote this to** emptiness of `d!=0`, emptiness of the `d=0` cube core, closure of `(6,9)`, a polynomial Keller pair, or JC2.

**Smallest valid successor:** four separate bounded gates — constant-`s` fibres, monomial-`s` fibres with jets `(1.3)`, ramified common Kuranishi rows including moving constants, and the `d=0` cube core with quotient `(3.4)`. No generic coefficient search, no AWS.
