# Hostile different-model review — GCD3 `(6,9)` common-cubic first gate

| Field | Value |
|---|---|
| Claim under review | Frozen producer first common-cubic gate: genuine `(6,9)` pairs admit an exact cubic-Kummer normalization that splits into an aligned branch and a cube-core mismatch branch; full-cubic boundary reduction type-fails without orbit degree three; the normalized constant-`W` scheme is exactly the common-cubic surface union one Davenport--Stothers curve, meeting only at the triple cubic; the eight high source rows reduce to five moving coefficients plus essential `kappa`; a pure DS source path is ODE/boundary-empty, but entry from the full `(6,9)` system is not derived |
| Overall verdict | **CONFIRMED** |
| Smallest failing identity | none |
| Smallest missing hypothesis | none that breaks a numbered claim (non-blocking: the scheme-theoretic intersection of the two primes is the length-two fat point `(a_0,a_1,a_2,a_3,a_4^2)`, which the producer correctly classifies only after taking radical; emptiness of the noncube ODE branch uses the historical `3\|deg(h)`, not a gap in `5e+7n=1`) |
| Evidence tier | independent hand derivation of the `y^{13}` identity, depression, Kummer weights, Euler/Wronskian calculus, and every finite-place/infinity valuation case; independently solved triangular source Jacobian and frozen-`W` systems; second-engine Singular primary decomposition (`lp` order, both GTZ and SY) of the residual scheme; official Rikkyo Shioda PDF and ICM-archive Zannier PDF, hash-checked; unmodified rerun of both registered replays as regression only |
| Reviewer / model | Grok 4.6 (xAI). Different model family from the producer (OpenAI Codex, GPT-5 family) |
| Repo | `/Users/dc/code/math/jc2` |
| Git HEAD | `6f2e49e63d74493910fa357a8adc82f0e40d219a` (matches the charged basis) |
| Review window (UTC) | 2026-08-24T13:44:21Z – 2026-08-24T13:58:00Z |
| Python | uv-pinned CPython 3.11.11 + SymPy `1.14.0` (registered replay and independent reconstruction) |
| Singular | `/opt/homebrew/bin/Singular` 4.4.1 |
| Host | `dc-mbp-m2.local`, Darwin arm64 |

Producer, freeze, and cited reviewed history stop reread in full before any verdict:

- `xmodel/gcd3-69-common-cubic-first-gate-20260824.md` (SHA-256 `f63bf74fd1013c74645f9f7fe9292db69199572b390b5b19d160c5ed13b373e8`)
- `cases/gcd3_69_common_cubic_first_gate_20260824/MANIFEST.sha256` (SHA-256 `ea2353e008b9ce1d52810fc792c23b3ce8c3246812e8912432dbf37677707e2c`)
- `cases/gcd3_69_common_cubic_first_gate_20260824/FREEZE.sha256` (SHA-256 `65370031b04014f96efc3ac814477a6689d5d5fef6b2695066ba6d60658ee585`)
- `xmodel/as109-partial-y-history-stop-20260824.md` (SHA-256 `6994dd6bc1642122ba549be474d2465203faf554d93da5146ecb212dbaaf89fe`)
- `xmodel/as109-partial-y-history-review-grok-20260824.md` (SHA-256 `f9d547f0f17dc3557ed8edce19912b4930dc2125542c7f9b3e4782c554a03afd`)

The committed basis is exactly `6f2e49e63d74493910fa357a8adc82f0e40d219a`. Named producer artifacts remain uncommitted on top of that basis. No producer, case, canonical, ladder, or notes file was edited. No enumerator, exponent rectangle, or AWS helper was written into the tree. Independent reconstruction lived only in `/tmp`.

Do not import a persistent common root, orbit degree three, pure Davenport--Stothers entry, polynomial Kummer depression, or a nonlinear `(6,9)` exclusion. The producer does not import those either.

---

## Promotion

**Accept `KUMMER NORMALIZATION SPLITS; FULL-CUBIC BOUNDARY REDUCTION TYPE-FAILS WITHOUT ORBIT DEGREE THREE; THE NORMALIZED CONSTANT-W SCHEME IS EXACTLY COMMON-CUBIC UNION ONE DAVENPORT--STOTHERS CURVE; HIGH SOURCE ROWS REDUCE TO FIVE COEFFICIENTS PLUS KAPPA; A PURE DS SOURCE PATH IS CONDITIONALLY EMPTY` at the stated scopes.**

- A genuine pair of actual `y`-degrees `(6,9)` with `a_6=h^2`, `b_9=h^3` has `delta=3A-2B` constant. Nontrivial cubic Kummer action forces `delta=0`. A cube core only makes `h` a constant times a polynomial cube and leaves `delta\neq 0` live. The change `z=sy+r` is over `L=k(x)(s)`, not a polynomial source automorphism; `P(x,0)=f(r)` and `Q(x,0)=g(r)` are polynomial and need not vanish.
- A chosen polynomial boundary root licenses reduction only modulo its minimal polynomial over the coefficient field of `K(1,z)`. Full-cubic reduction is a `TYPE-FAIL` without a separately proved orbit of degree three. Discriminant nonvanishing does not supply that orbit.
- After the high Wronskian rows, the residual ideal in `(a_0,\ldots,a_4)` has radical exactly `P_{\mathrm{common}}\cap P_{\mathrm{DS}}`. These are the only reduced components. They meet set-theoretically only at the triple-cubic origin. The original residual scheme is nonreduced along the common component. The DS parameterization, difference `f^3-g^2`, constant Wronskian `378\lambda^7`, and resultant `(3^9 7^2/2^5)\lambda^{27}` are exact.
- The eight high source rows integrate to five moving `a_i` plus essential `kappa=c_3` after Kummer descent and constant target gauges. On any path that persists on the common component one has `f=K^2`, `g=K^3+kappa K` and vanishing source bracket. An associated-graded common point does not prove that persistence.
- Conditional on pure DS entry after aligned depression, the Keller equation is `(\lambda^7)'=j/(81s)`. Exact valuations exclude the noncube Kummer case under the historical `3\mid\deg(h)`, and both polynomial boundaries exclude the remaining cube case. This is a closed conditional branch, not a closure of `(6,9)`.

**Do not promote this to:** a polynomial identity `z=sy+r`; orbit degree three; a persistent filtered common root; derivation that an aligned `(6,9)` trajectory enters the pure DS curve; closure of the cube-mismatch branch `delta\neq 0`; a solution of the four lower Pfaffian rows or the terminal Keller row; a Keller pair of type `(6,9)`; a nonlinear `(6,9)` exclusion; or a JC2 decision.

**Smallest valid successor.** Solve the four lower Pfaffian rows and the terminal row of the exact five-variable-plus-`kappa` form, componentwise, retaining the chosen minimal boundary factor `m_\rho` rather than the full cubic. If the associated-graded arc lands on the DS prime, apply the conditional Section 7; if it lands on the common primary, compute the first nonzero Kuranishi row separately on the squarefree and double strata. Run `delta\neq 0` as an independent parallel branch. Do not open a generic coefficient rectangle or AWS.

---

## Quarantine

No result here proves or disproves JC2, constructs or excludes a characteristic-zero Keller pair of type `(6,9)`, or closes the cube-mismatch branch. Producer strings `PASS-GCD3-69-FIRST-COMMON-CUBIC-GATE` and `PASS-GCD3-69-CONSTANT-W-SCHEME` were not used as evidence; the Jacobian identities, the eight `b`-rows, the four residuals, the primary decomposition, the DS family, the jets, and the valuation lattice were re-derived. Literature (Shioda, Zannier, the unpaid Stothers citation) was source-checked only for the historical claims actually used; the component calculation stands independently. The reviewed partial-`y` history stop is consumed only for actual degrees `(6,9)` with `a_6=h^2`, `b_9=h^3` and the residue `3\mid H`; it does not license a filtered common root.

---

## Scope (not enlarged)

Exact polynomial identities, a Kummer-weight split of the first depression, a `TYPE-FAIL` of full-cubic *boundary* reduction, filtration-sensitive linear/quadratic/Artinian controls, a complete reduced classification of the normalized constant-`W` scheme at degrees `(6,9)`, high-row reduction to five coefficients plus `kappa`, and a conditional local-valuation exclusion of a pure DS source path. Actual `(6,9)` Keller pairs, nonlinear exclusion, polynomial depression, orbit degree three, filtered persistence, cube mismatch, and JC2 remain out of scope.

---

## Headline and subclaim table

| # | Exact subclaim | Verdict | What would have flipped it |
|---|---|---|---|
| 1 | From actual `y`-degrees `(6,9)` and `a_6=h^2,b_9=h^3`, the `y^{13}` identity is `s^{14}(9A'-6B')`, depression is `r=A/6`, residual mismatch is `-delta/2` with `delta=3A-2B` constant. Nontrivial cubic Kummer forces `delta=0`; a cube core only makes `h` a constant times a polynomial cube and leaves `delta\neq 0` live. `z=sy+r` is over a coefficient extension; both boundary values are polynomial and need not vanish | **CONFIRMED** | leftover `s'` terms in the `y^{13}` row; constants of `L/k(x)` larger than `k`; weight of `A` or `B` not `1`; `3\mid\deg(h)` used as if it made `h` a cube; `z=sy+r` treated as a polynomial source auto; `P(x,0)` forced to vanish |
| 2 | The triangular `z^{12},\ldots,z^5` source system integrates to eight constants; Kummer kills `c_7,c_5,c_4,c_2,c_1`; constant target gauges remove `c_6,c_0`; the surviving form is five moving `a_i` plus essential `kappa=c_3`. On a persistent common component this is exactly `f=K^2,g=K^3+kappa K` with zero source bracket; an associated-graded common point does not prove persistence | **CONFIRMED** | a non-closed high-row one-form; a weight-zero extra constant besides `c_6,c_3,c_0`; `kappa` absorbed into constant-`W` without lower rows; source bracket of `(K^2,K^3+kappa K)` nonzero; persistence inferred from one graded point |
| 3 | UFD gives `F_0=K^2,G_0=K^3`; the depressed cubic and its squarefree/double/triple strata are exact. A boundary equation licenses reduction only modulo `m_\rho`, not the full cubic without orbit degree three. The split control `K=z^3-t^2z`, `rho=0`, `phi=zt^5`, `psi=3Kphi/2` is a `TYPE-FAIL` of full-cubic *boundary* reduction | **CONFIRMED** | a homogeneous pair of degrees `(6,9)` with vanishing binary Jacobian not a cubic power; `Delta\neq 0` used as orbit degree three; `phi` divisible by `K` on the split control; the type-fail promoted to a Jacobian-row refutation |
| 4 | `L_K=K\{K,2psi-3Kphi\}`; the constant row is a nonzero tangent cokernel class; under exact zero-RHS filtration, `q_2=9phi^2 K_z\pmod{K}` hence `K\mid phi` on the squarefree stratum, with the three displayed coefficient rows. RHS/boundary caveat is load-bearing. The double- and triple-root two-jets survive over `k[e]/(e^3)` and are not characteristic-zero Keller pairs | **CONFIRMED** | a linearized bracket not divisible by `K`; gauges enlarging the image to constants; `q_2=0\pmod{K}` forcing `K\mid phi` without reducedness or the filtration hypothesis; the jets having Jacobian a nonzero constant in characteristic zero |
| 5 | All eight frozen `b`-rows and four residual equations reconstruct uniquely. The radical is exactly `P_{\mathrm{common}}\cap P_{\mathrm{DS}}`; these are the only reduced components and meet only at the triple-cubic origin. The original residual scheme is nonreduced along the common component. DS parameterization, `f^3-g^2`, `W=378\lambda^7`, and the exact nonzero resultant hold | **CONFIRMED** | a third associated prime; `I` already radical; a geometric intersection point with `Delta\neq 0` or a double-root common cubic; resultant vanishing for `lambda\neq 0`; `W` not constant on the DS curve |
| 6 | The DS curve meets the common component only at the triple point; `f_lambda(0)` first turns on at `lambda^3` and the constant row at `lambda^7`. This is a negative control against filtered boundary persistence. Historical claims used from Shioda/Zannier check; the component calculation does not depend on them | **CONFIRMED** | a common root of `f_lambda,g_lambda` for some `lambda\neq 0`; constant `W` appearing at order `<7`; literature used as evidence for primary decomposition; a persistent filtered common root inferred from the leading layer |
| 7 | Under—and only under—the pure-entry hypothesis: weighted Euler, `J_{(\lambda,z)}=567\lambda^6`, chain rule, and `(lambda^7)'=j/(81s)`. Every finite-place and infinity case of `(7.4)`–`(7.8)` holds, including `h` constant, cancellation, leading coefficients, and why historical `3\mid\deg(h)` forces the cube-core form. Both polynomial boundaries then contradict the nonzero resultant. No valuation case was omitted | **CONFIRMED** | a solution of `5e+7n=1` with `e>0` and `2e+3n\neq 0` outside `k\geq 1`; cancelled `2e+3n=0` of valuation `0`; `h` constant giving nonzero `j`; `r\geq 2` with vanishing leading coefficient; a balanced boundary with `f_1(\xi)=g_1(\xi)=0`; pure entry treated as derived |
| 8 | Maximum licensed promotion is exactly the list in the prompt. The gate does not solve the four lower Pfaffian rows, the terminal Keller row, filtered persistence, cube mismatch, `(6,9)`, or JC2. Those lower rows, treated componentwise with the true minimal boundary factor, together with the independent cube-mismatch branch, are the smallest honest successor | **CONFIRMED** | a hidden solution of `z^4,\ldots,z^0`; promotion of associated-graded commonness to persistence; a claim that the successor is a generic coefficient search |

All remarks below are non-blocking unless marked otherwise. None changes a numbered verdict.

---

## Replay and hashes

Frozen hashes, recomputed on the charged tree, match the launch prompt, `MANIFEST.sha256`, and `FREEZE.sha256`:

| Artifact | SHA-256 | Match |
|---|---|---|
| `xmodel/gcd3-69-common-cubic-first-gate-20260824.md` | `f63bf74fd1013c74645f9f7fe9292db69199572b390b5b19d160c5ed13b373e8` | prompt, `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_common_cubic_first_gate_20260824/MANIFEST.sha256` | `ea2353e008b9ce1d52810fc792c23b3ce8c3246812e8912432dbf37677707e2c` | prompt (self-hash) |
| `cases/gcd3_69_common_cubic_first_gate_20260824/FREEZE.sha256` | `65370031b04014f96efc3ac814477a6689d5d5fef6b2695066ba6d60658ee585` | prompt (self-hash) |
| `cases/gcd3_69_common_cubic_first_gate_20260824/PREREGISTRATION.md` | `55ced70452072d141f17bb87d64797c842cd0af94f5d14c32c8806afa12c61aa` | `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_common_cubic_first_gate_20260824/replay.py` | `0ec1a7295cb9a3b090e1be2dfab1f730c12e2d8aeeec492c22932c9d720d3a94` | `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_common_cubic_first_gate_20260824/verify_constant_w_scheme.sing` | `ea4761f641e1778bbc3cfa9f7769a9129ab1a3ca0ddd6d8944431400645eb06a` | `MANIFEST`, `FREEZE` |
| `xmodel/as109-partial-y-history-stop-20260824.md` | `6994dd6bc1642122ba549be474d2465203faf554d93da5146ecb212dbaaf89fe` | preregistration |
| `xmodel/as109-partial-y-history-review-grok-20260824.md` | `f9d547f0f17dc3557ed8edce19912b4930dc2125542c7f9b3e4782c554a03afd` | preregistration |

The case directory contains exactly those five files. No enumerator, exponent rectangle, or AWS helper is present.

Registered commands, rerun unmodified from the repository root:

```sh
uv run --offline --no-project --with sympy==1.14.0 python \
  cases/gcd3_69_common_cubic_first_gate_20260824/replay.py

Singular -q \
  cases/gcd3_69_common_cubic_first_gate_20260824/verify_constant_w_scheme.sing
```

Both exit 0. Exact output:

```text
PASS-GCD3-69-FIRST-COMMON-CUBIC-GATE
normalization=KUMMER-ALIGNED-OR-CUBE-MISMATCH
binary_leading_structure=H^2,H^3
high_row_reduction=FIVE-COEFFICIENTS-PLUS-KAPPA
discriminant_strata=SQUAREFREE,DOUBLE,TRIPLE
full_cubic_boundary_reduction=TYPE-FAIL-WITHOUT-ORBIT-DEGREE-3
linear_constant_row=TANGENT-ONLY-NONZERO-COKERNEL-CLASS
squarefree_quadratic_residue=RHS-FILTRATION-CONDITIONAL
double_and_triple_component_residue=TWO-JET-SURVIVORS
nonlinear_constant_w_bypass=UNIQUE-ORDER3-DS-CURVE
ds_first_constant_order=lambda^7=epsilon^14
ds_persistent_common_boundary_root=false
pure_ds_source_ode=(lambda^7)'=j/(81s)
pure_ds_noncube_branch=VALUATION-EMPTY
pure_ds_cube_branch=POLYNOMIAL-BOUNDARY-EMPTY
nonlinear_69_closure=false
keller_pair_found=false
jc2_inference=false

PASS-GCD3-69-CONSTANT-W-SCHEME
radical_components=COMMON-CUBIC-SURFACE,UNIQUE-DS-CURVE
component_intersection=TRIPLE-CUBIC-ORIGIN-ONLY
ds_constant_w=(189/8192)*a4^7
ds_persistent_common_root=false
```

Those PASS strings are regression only. The independent reconstruction of Claims 1–7 is the evidence.

Independently recomputed primary-source hashes that match the producer table:

| Source | SHA-256 | Match |
|---|---|---|
| Shioda, official Rikkyo `AA00610867_54-01_04.pdf` | `467701925109586976ca8f89ec614ee95c5ad740084b969a93ba3795b0cdb740` | producer §5.1 |
| Zannier, ICM journal-archive `aa/aa71/aa7122.pdf` | `b629733a8c7c64007110e06e5ffc73212eb4b87bcbd6dbcf5416cac485c51a2d` | producer §5.1 |

Shioda §1, display (4), records `St(m)=1` for `m=1,2,3,4`. Shioda §5, the `m=3` (Birch) display, is exactly `(5.7)` at `lambda=1`, including the `63/2` linear term; the difference polynomial there is `(27/4)(4t^4+13t^2+32)`, matching `(5.8)`. Zannier’s introduction states existence of equality cases of Davenport’s bound for every positive order, with `deg(f,g)=(2n,3n)`. Stothers’ paywalled 1981 paper was not consumed; it is not needed for the new algebra.

Independent reconstruction, second derivation or second engine for every load-bearing finite identity: 123 exact SymPy assertions on a solver path that does not import producer formulas, plus Singular primary decomposition in monomial order `lp` by both GTZ and SY. The residual generators so obtained coincide with the producer’s `(e_4,e_3,e_2,e_1)`. Both algorithms return exactly two primes, `P_{\mathrm{common}}` and `P_{\mathrm{DS}}`; the radical equals their intersection; the DS primary equals its prime; the common primary is properly contained in its prime (`P` has three extra generators modulo `Q`); `vdim(P_{\mathrm{common}}+P_{\mathrm{DS}})=2` with radical the origin.

---

## Claim 1 — top row and Kummer split

**CONFIRMED.**

Let `P=a_6 y^6+\cdots`, `Q=b_9 y^9+\cdots` be a genuine pair, and take the reviewed UFD `a_6=h^2`, `b_9=h^3` after constant target scalings. Put `s^3=h` in `L=k(x)(s)`, and write `a_6=s^6`, `b_9=s^9`, `a_5=s^5 A`, `b_8=s^8 B`. Direct expansion, with all four product rules, gives

```text
8 a_6' b_8 + 9 a_5' b_9 - 6 a_6 b_8' - 5 a_5 b_9'
  = 48 s^{13} s' B + 45 s^{13} s' A + 9 s^{14} A'
    - 48 s^{13} s' B - 6 s^{14} B' - 45 s^{13} s' A
  = s^{14}(9A'-6B').
```

The `s'` terms cancel. The same combination is `3 s^{14} delta'` for `delta=3A-2B`, so the vanishing `y^{13}` row places `delta` in the constant field of `L`. Because `k` is algebraically closed of characteristic zero and `L/k(x)` is algebraic, that constant field is `k`.

Starting from `z_0=sy`, the translation `z=z_0+r` with `r=A/6` kills the `z^5` coefficient of `P`. The `z^8` coefficient of `Q` becomes `B-9r=B-3A/2=-delta/2`. Independently checked on the truncated polynomials `(z-r)^6+A(z-r)^5` and `(z-r)^9+B(z-r)^8`.

Galois: `sigma(s)=omega s` with `omega^3=1\neq omega`. The source coefficients `a_5,b_8` are fixed, so `A=a_5/s^5` and `B=b_8/s^8` have weight `-5\equiv 1` and `-8\equiv 1` modulo three. Hence `sigma(delta)=omega delta`. Combined with `delta\in k`, this forces `delta=0` whenever the Kummer extension is nontrivial.

If `h` is a cube in `k(x)`, Gauss’s lemma puts `h` equal to a constant times a polynomial cube, so `s` may be taken in `k[x]` (`k` algebraically closed). There is then no nontrivial Kummer action, and `delta\neq 0` remains a live normal-form branch. The historical condition `3\mid\deg(h)` does not make `h` a cube: `h=x(x-1)(x-2)` has degree three and is cube-free. That is the split the producer claims, and it is the correct split.

Even after alignment, `z=sy+r` is an identity in `L[y]`, not a polynomial source automorphism. The chain rule

```text
J_{(x,y)}(P,Q)=s(f_x g_z-f_z g_x)
```

holds because the two `z_x` summands cancel in the determinant (independently checked on a generic depressed pair). The boundary provenance is `z|_{y=0}=r` and `P(x,0)=f(r)`, `Q(x,0)=g(r)`. The right-hand sides lie in `k[x]`; they are not identically zero, and forcing both to vanish would make `y` divide both coordinates, hence divide the Jacobian.

No identity failed.

---

## Claim 2 — eight high source rows

**CONFIRMED.**

Continue in the aligned nontrivial-Kummer branch, with

```text
f=z^6+a_4 z^4+a_3 z^3+a_2 z^2+a_1 z+a_0,
g=z^9+b_7 z^7+\cdots+b_0.
```

The `z^{12},\ldots,z^5` coefficients of `f_x g_z-f_z g_x` form a triangular first-order system for `(b_7',\ldots,b_0')`. Independently, each row is linear homogeneous in the velocities `(a_i')` with no inhomogeneous term, so it is a closed polynomial one-form on `(a_4,\ldots,a_0)` and integrates to a unique potential plus a constant `c_j`. The four displayed formulas in `(1.9)` reconstruct exactly, including the cross terms `(7/6)a_4 c_7` and `(7/6)a_3 c_7+a_4 c_6`. The `c=0` slice coincides with the frozen-`W` solution of Claim 5.

A coefficient of `z^j` has Kummer weight `-j\bmod 3`, and so does `c_j`. The indices with nonzero weight in `{0,\ldots,7}` are exactly `{7,5,4,2,1}`, so nontrivial descent forces `(1.10)`. The remaining constants are `c_6,c_3,c_0`. The constant target shear `g\mapsto g-c_6 f` preserves the source Jacobian and removes `c_6`; target translation removes `c_0`. What survives is

```text
g=g_0(a_0,\ldots,a_4)+kappa(z^3+(a_4/2)z+a_3/2),
```

with `g_0` the eight-row zero-constant solution. Independently, this reduced pair still kills `z^{12},\ldots,z^5`. Four lower Pfaffian rows and the terminal row `z^0=j/s` remain. That is exactly the five-plus-`kappa` count claimed.

On the common-cubic locus `a_4=2u`, `a_3=2v`, `a_2=u^2`, `a_1=2uv`, `a_0=v^2` one has `f=K^2` and `z^3+(a_4/2)z+a_3/2=K`, hence `g=K^3+kappa K`. For any `x`-motion of `(u,v)`,

```text
(2K\,dK)\cdot\partial_z(K^3+kappa K)-\partial_z(K^2)\cdot(3K^2+kappa)\,dK=0.
```

So a path that *persists* on `(1.12)` has identically vanishing source Jacobian and cannot be Keller. The `kappa K` summand is a genuine source integration constant: the `z`-Wronskian on that pair is `-4 kappa K^2 K_z`, which is constant only if `kappa=0`. It does not belong to the frozen constant-`W` classification of Section 5 unless the lower rows force `kappa=0`. An associated-graded common-cubic point is one fibre of this family and does not prove persistence through the lower filtration. The producer does not claim otherwise.

No identity failed.

---

## Claim 3 — cubic provenance and strata

**CONFIRMED.**  (The producer’s `TYPE-FAIL` of full-cubic *boundary* reduction is the correct conclusion of this claim, not a failure of the claim.)

Let `F_0,G_0` be monic homogeneous binary forms of degrees six and nine with vanishing binary Jacobian. Euler gives `t\{F_0,G_0\}=6 F_0(G_0)_z-9 G_0(F_0)_z=0`, equivalently `(G_0^2/F_0^3)_z=0`. Homogeneity forces the degree-zero rational function `G_0^2/F_0^3` to be a constant, and monicity makes the constant `1`. Unique factorization in `k[t,z]` then yields `F_0=K^2`, `G_0=K^3` for a monic homogeneous cubic `K`: every exponent in `F_0` is even because it becomes even after multiplication by three. This is a binary-leading identity, not a claim that the global pair is `(K^2,K^3)`.

Absence of the `z^5` and `z^8` rows kills the `z^2 t` coefficient of `K`, because that coefficient produces `2p\, t z^5` in `K^2` and `3p\, t z^8` in `K^3`. Thus `K=z^3+u t^2 z+v t^3` with discriminant `Delta=-4u^3-27v^2`, independently checked. The geometric split `(2.3)` is the standard depressed-cubic stratification; the double-root parameterization `u=-3a^2`, `v=2a^3` is the expansion of `(z-at)^2(z+2at)`.

For a boundary root `rho` of `K(1,z)` over the coefficient field `K_0`, `H(rho)=0` if and only if the minimal polynomial `m_rho` divides `H`. Full reduction modulo `K` therefore requires `m_rho=K`, i.e. an orbit of degree three. Discriminant nonvanishing does not supply this: over `K_0` a squarefree cubic may be irreducible (orbit 3), linear times irreducible quadratic (orbit 1 or 2), or three linear factors (orbit 1). Independently checked on `z^3-2`, `z(z^2-2)`, and `z(z-1)(z+1)`, all of nonzero discriminant. After base change to a splitting field the étale algebra has three idempotents, but a section already defined over `K_0` occupies one of them. Descent does not manufacture the other two vanishings.

The split control `(3.2)` is exact: `L_K(phi,psi)=0`, both first-order boundaries vanish at `rho=0`, and `phi|_{t=1}` takes values `(0,1,-1)` at the three roots, hence is divisible by the selected linear factor and not by `K`. This is a `TYPE-FAIL` of a full-cubic *boundary* reduction. It does not refute a full-cubic conclusion derived from extra Jacobian rows, and the producer does not claim that it does.

No identity failed.

---

## Claim 4 — linear, quadratic, and singular controls

**CONFIRMED.**

With `{A,B}=A_t B_z-A_z B_t` and normalized perturbations of degrees six and nine,

```text
{phi,K^3}+{K^2,psi}
  = 3K^2 {phi,K} + 2K {K,psi}
  = K {K, 2psi-3K phi},
```

because `{K,K phi}=K{K,phi}`. Independently expanded against a generic normalized `(phi,psi)`, this is an identity, not a congruence. In particular every linearized bracket is divisible by `K`, so as a polynomial it is never a nonzero constant. A requested nonzero constant `c` has resultant `Res_z(K(1,z),c)=c^3\neq 0`. Quotienting the *domain* by source, target, or `(u,v)` gauges cannot enlarge the image. This is a tangent obstruction; Section 5 supplies the nonlinear bypass.

Vanishing of `{K,2psi-3K phi}` at these degrees, after the leading-term normalization that already removed `z^9` and `z^8`, forces `psi=(3/2)K phi`. The quadratic bracket is then `{phi,psi}=(3/2)phi{phi,K}`. Euler on `phi` and `K` reduces this, modulo `K` and at `t=1`, to `9 phi^2 K_z`. Independently checked by remainder. On `Delta\neq 0` the quotient `K_0[z]/(K)` is reduced and `K_z` is a unit, so `q_2=0\pmod{K}` if and only if `K` divides `phi`, *provided* the constant row and both boundary values are still absent at this filtration order. Reducing `phi=p_4 z^4+\cdots+p_0` modulo `K=z^3+uz+v` produces exactly the three rows `(4.6)` and leaves the two common-cubic tangent directions. On the split control the quadratic residues are `(0,18,18)`.

If the constant row first appears at this order the equation is `9 phi^2 K_z=c\pmod{K}`; if a boundary polynomial contributes, `phi(rho)` need not vanish. The DS curve of Claim 5 is the exact delayed-control: first boundary term at `lambda^3`, constant bracket at `lambda^7`.

On the nonreduced singular quotient, `q_2=0` only forces `rad(K)\mid phi`. The two displayed jets reconstruct independently:

```text
K=(z-t)^2(z+2t),  rho=-2t,
{K^2+e phi, K^3+e psi_1+e^2 psi_2}=-(9/8) e^3 t^{11}(z+2t)(5t+4z);

K=z^3,  rho=0,
{K^2+e phi, K^3+e psi_1+e^2 psi_2}=-(9/2) e^3 t^{11} z^2.
```

Both vanish over `k[e]/(e^3)`, satisfy the selected-root boundaries, and fail to have Jacobian a nonzero constant in characteristic zero. They are Artinian controls, not Keller pairs. The producer does not treat them as such.

No identity failed.

---

## Claim 5 — complete normalized constant-`W` scheme

**CONFIRMED.**

Now `W=2f g_z-3 f_z g` with coefficients frozen in `x`. The `z^{14}` and `z^{13}` coefficients vanish by the same leading cancellation as the source top rows. The `z^{12},\ldots,z^5` coefficients uniquely solve `b_7,\ldots,b_0`. Independently, by solving each coefficient for one `b_j` in descending order:

```text
b_7=3 a_4/2,
b_6=3 a_3/2,
b_5=3(4a_2+a_4^2)/8,
b_4=3(2a_1+a_3 a_4)/4,
b_3=(24 a_0+12 a_2 a_4+6 a_3^2-a_4^3)/16,
b_2=3(4 a_1 a_4+4 a_2 a_3-a_3 a_4^2)/16,
b_1=3(32 a_0 a_4+32 a_1 a_3+16 a_2^2-8 a_2 a_4^2-8 a_3^2 a_4+a_4^4)/128,
b_0=(24 a_0 a_3+24 a_1 a_2-6 a_1 a_4^2-12 a_2 a_3 a_4-2 a_3^3+3 a_3 a_4^3)/32.
```

The `z^4,z^3,z^2,z` rows then become nonzero rational multiples of the producer’s `(e_4,e_3,e_2,e_1)`, with multipliers `15/64`, `33/128`, `3/32`, `3/128`. The `z^0` row is the constant value of `W`; it is not required to vanish. Both advertised families annihilate the four residuals: the common cubic `(z^3+uz+v)^2,(z^3+uz+v)^3` and the DS slice `a_4=4lambda`, `a_3=a_1=0`, `a_2=10 lambda^2`, `a_0=6 lambda^3`.

Second engine, ring order `lp` rather than the producer’s `dp`, both `primdecGTZ` and `primdecSY`: exactly two primary components; associated primes equal to

```text
P_common=(4a_2-a_4^2,\ 2a_1-a_3 a_4,\ 4a_0-a_3^2),
P_DS=(a_3,\ a_1,\ 8a_2-5 a_4^2,\ 20a_0-3 a_2 a_4);
```

`radical(I)=P_{\mathrm{common}}\cap P_{\mathrm{DS}}`. The DS primary equals `P_{\mathrm{DS}}` (reduced). The common primary is properly contained in `P_{\mathrm{common}}` (three extra prime generators survive reduction modulo the primary). Thus the original residual scheme is nonreduced along the common component and reduced along DS, matching the tangent and two-jet controls of Section 4. This is a set-theoretic classification of `V(I)`, not a claim that `I` is radical.

The two primes meet set-theoretically only at the origin: substituting both systems yields `3 a_4^2=0`, hence `a_4=a_3=a_2=a_1=a_0=0` over characteristic zero, i.e. `K=z^3`. Independently, `radical(P_{\mathrm{common}}+P_{\mathrm{DS}})=(a_0,\ldots,a_4)`. Scheme-theoretically the sum is `(a_0,a_1,a_2,a_3,a_4^2)` of vector-space length 2; the producer takes the radical and does not claim a reduced intersection scheme. No nonlinear constant-`W` branch meets a squarefree or double-root point of the common surface.

On the DS parameterization, a second expansion gives

```text
f_lambda^3-g_lambda^2=(27/4) lambda^7 (4z^4+13 lambda z^2+32 lambda^2),
2 f_lambda (g_lambda)_z-3 (f_lambda)_z g_lambda=378 lambda^7,
Res_z(f_lambda,g_lambda)=(3^9 7^2/2^5) lambda^{27}.
```

The last identity was obtained twice, from `sympy.resultant` and from `Poly.resultant`. At `lambda=1` this is Birch’s order-three example as reproduced by Shioda. For `lambda\neq 0` the resultant is nonzero, so there is no persistent common boundary root. The identity `f H'-3 f' H=-(2fg'-3f'g)g` is an algebraic tautology, so a nonzero constant Wronskian at degrees `(6,9)` is precisely an extremal order-three Davenport--Stothers pair. Under `a_4=4lambda` one has `(189/8192) a_4^7=378 lambda^7`, reconciling the two normalizations. Under `lambda=epsilon^2` the constant first appears at order `epsilon^{14}`.

No identity failed.

---

## Claim 6 — boundary timing and literature scope

**CONFIRMED.**

At `rho=0`,

```text
f_lambda(0)=6 lambda^3,     g_lambda(0)=0,
```

while `W=378 lambda^7`. Both leading forms vanish at the triple root when `lambda=0`, but one boundary turns on at order `lambda^3` and the constant row only at order `lambda^7`. That is four orders of delay, and it is the exact negative control against promoting a leading common root to a filtered common root. At fixed `lambda\neq 0` a persistent common root is independently impossible: `W` would vanish at that root, contrary to `378 lambda^7\neq 0`, and the resultant `(5.9)` is the symmetric certificate.

This matches the source provenance `(1.6)`: multiplying by the leading weight can make a regular polynomial boundary vanish in the associated graded, with the first regular term allowed later. An additional order statement is required before persistence can be asserted. The producer does not assert it.

Literature. Official Shioda PDF hash matches; §1 records `St(3)=1` and §5 records exactly `(5.7)` at `lambda=1`. Official ICM-archive Zannier PDF hash matches; the paper proves existence of extremal examples in every order. Those facts are historical and supply the named control. They are not used as evidence for `(5.3)`. Stothers 1981 is cited for attribution and is explicitly not consumed. That is the correct scope.

No identity failed.

---

## Claim 7 — conditional pure-DS closure

**CONFIRMED.**  No valuation case was omitted; no counterexample is frozen.

The load-bearing hypothesis is exactly the one written: after aligned Kummer depression, the complete normalized coefficient path is `(f_lambda(x),g_lambda(x))` of `(5.7)`, with all lower-weight integration constants absent. That entry is not derived in this gate.

Weighted Euler `z\partial_z+2lambda\partial_lambda` of weights `(1,2)` reconstructs independently on both coordinates, and

```text
2 lambda J_{(lambda,z)}=3 W=1134 lambda^7,
J_{(lambda,z)}=567 lambda^6.
```

The chain rule of Claim 1, including `x`-dependence of `s,r`, still cancels `z_x`. A pure DS path therefore satisfies Keller if and only if `567 s lambda^6 lambda'=j`, equivalently `(lambda^7)'=j/(81s)` because `567/7=81`.

Kummer weight two gives `lambda=s^2 q` with `q\in k(x)` and `s^3=h`. Direct differentiation of `lambda^7=h^4 s^2 q^7` converts `(7.3)` into `(7.4)`. Independently, `189 h^4 q^6(2h'q+3h q')` equals the expanded `81\cdot 7\cdot h^4 q^6\bigl(\tfrac{2}{3}h' q+h q'\bigr)`.

Finite places. Write `e=v(h)\geq 0`, `n=v(q)`. Locally `h=C t^e(1+\cdots)`, `q=D t^n(1+\cdots)`, the derivative combination has leading factor `CD t^{e+n-1}(2e+3n)`, so cancellation occurs if and only if `2e+3n=0`.

- If `e=0` and `n\neq 0`, the `h q'` term has valuation `n-1` and total valuation `7n-1=0` is impossible in integers. Thus `e=0` forces `n=0` at that place.
- If `e>0` and `n=0`, then `v(2h'q)=e-1<e\leq v(3h q')`, no cancellation, and `5e-1=0` is impossible. So `n\neq 0` at every zero of `h`.
- If `e>0`, `n\neq 0`, and `2e+3n\neq 0`, constancy forces `5e+7n-1=0`. Because `gcd(5,7)=1`, every integer solution is `e=3+7k`, `n=-2-5k`. The condition `e>0` and non-cancellation excludes `k\leq 0` (`k=0` is precisely `2e+3n=0`; `k\leq -1` has `e\leq -4`, a pole of the polynomial `h`). Thus `k\geq 1` and `2e+3n=-k\neq 0`.
- If `2e+3n=0` with `e>0`, then `n=-2e/3` and `v(h^4 q^6)=0`, but `v(2h'q+3h q')\geq e+n=e/3>0`. For pure monomials the combination is *identically* zero; for a unit perturbation `h=C t^3(1+c_1 t)`, `q=D t^{-2}(1+d_1 t)` it equals `CD\bigl((3d_1+2c_1)t+5 c_1 d_1 t^2\bigr)`, valuation exactly `1`. In every subcase the left-hand side of `(7.4)` vanishes at the place and cannot be a nonzero constant. Mixed configurations (some cancelled zeros, some of type `(7.5)`) likewise vanish at the cancelled zeros.

Hence the divisor of `q` is supported exactly on the zeros of `h`. If `h` has no zero then `h` and `q` are both constant, the left-hand side of `(7.4)` is identically zero, and `j\neq 0` is contradicted. Thus `h` has `r\geq 1` distinct zeros.

Infinity. Logarithmic derivatives give

```text
2h'q+3h q'=h q \sum_i (-k_i)/(x-a_i),
```

so the full left-hand side of `(7.4)`, up to the constant `189`, equals `-C^5 D^7 N(x)` where `N` is the numerator of `\sum k_i/(x-a_i)`, of degree `r-1`, with leading coefficient `\sum k_i\neq 0` because each `k_i\geq 1`. Constancy forces `r=1`. Thus `h=C(x-a)^{3+7k}`. The reviewed historical residue `3\mid\deg(h)` forces `3\mid k`. Writing `k=3ell` with `ell\geq 1` yields `(7.8)` and places every rational solution of the pure-DS ODE in the *cube* core. There is no noncube/Kummer solution *on this residue*. (Without `3\mid H` the lattice point `k\not\equiv 0\pmod{3}` would be a noncube ODE solution in `L`; those pairs are already excluded by the history-stop shear, and are not in scope here.) The smallest history-compatible control is `h=x^{24}`, `s=x^8`, `q=x^{-17}`, `lambda=x^{-1}`, with source Jacobian factor `-567`.

Both polynomial boundaries. Let `t=x-a` and `v(lambda)=-ell<0`. For a boundary value `z=r(x)` of integer valuation `nu`, the four valuations in `f_lambda(r)` are `6nu`, `-ell+4nu`, `-2ell+2nu`, `-3ell`. Shifting by `3ell` yields `(3w,2w,w,0)` with `w=2nu+ell`. If `w\neq 0` the minimum is unique. If `w>0` it is `-3ell<0`; if `w<0` then `nu<0` (because `ell\geq 1`) and the minimum is `6nu<0`. In either case `f_lambda(r)` has a pole, contradicting `f(r)\in k[x]`. If `w=0`, all four terms of `f` and all five terms of `g` balance; regularity of both boundaries forces a common root of `f_1` and `g_1`, contradicting the nonzero resultant `(5.9)`. The odd-`ell` subcase never balances (`2nu=-ell` is then impossible in integers) and is already killed by unique-minimum. Poles of `r` away from `t=0` make `f_lambda(r)\sim r^6` pole while `lambda` is a unit, again contradicting polynomiality. The identically-zero section `r\equiv 0` has unique minimum `-3ell` from the `6lambda^3` term.

Therefore no rational pure-DS solution of `(7.3)` has both source boundary values in `k[x]`. Under the stated entry hypothesis the DS branch is empty. The cube-mismatch branch `delta\neq 0` and any trajectory with extra lower-weight constants remain open, as claimed.

No identity failed. No valuation case was omitted.

---

## Claim 8 — exact scope and successor

**CONFIRMED.**

The maximum licensed promotion is exactly the list in the prompt and in producer §8: Kummer-aligned versus cube-mismatch normalization; `TYPE-FAIL` of full-cubic boundary reduction without orbit degree three; the exact two-component constant-`W` classification; conditional exclusion of a pure DS source path; and high-row reduction to five variables plus `kappa`. The gate does not solve the four lower Pfaffian rows or the terminal Keller row, does not prove polynomiality of the rational depression data, does not close `delta\neq 0`, does not construct or exclude a Keller pair, and does not decide JC2. It does not promote an associated-graded common point to persistence of `(1.12)`, and it does not treat the Artinian jets as Keller pairs.

The smallest source-honest successor is the one written. The aligned branch now has an exact five-plus-`kappa` normal form whose remaining content is four Pfaffian rows and one terminal row; those rows must be read componentwise against the true minimal boundary factor `m_rho`, not against the full cubic. Landing on the DS prime re-uses Section 7; landing on the common primary requires a separate first Kuranishi row on each discriminant stratum; `delta\neq 0` is an independent parallel branch of the same width. A generic coefficient rectangle and AWS remain unlicensed. The history-stop’s older successor (a generic tangent cokernel question) has been discharged by this gate and must not be relaunched.

No identity failed.

---

## Non-blocking remarks

1. The scheme-theoretic intersection `P_{\mathrm{common}}+P_{\mathrm{DS}}` is the fat point `(a_0,a_1,a_2,a_3,a_4^2)` of length two. The producer classifies it via `radical`, which is the correct geometric statement and is the statement charged here.
2. Emptiness of the noncube pure-DS branch is the arithmetic `3\mid\deg(h)\Rightarrow 3\mid k`, not a claim that `5e+7n=1` has no noncube lattice points. The producer writes the historical hypothesis before `(7.8)` and is entitled to it on this residue.
3. In the registered Python replay the symbols `nu,ell` are declared `positive=True` in a matrix identity that in fact holds for all integers, including the physically relevant negative `nu`. The identity is correct; the positivity annotation is not used as a restriction.
4. Under `lambda=epsilon^2` the first boundary term is of order `epsilon^6`. The producer states the `lambda^3` timing in §4 and §6 and the `epsilon^{14}` timing only for the constant row. No confusion is licensed.
5. The constant-field sentence “the constant field of `L/k(x)` is `k`” uses algebraic closure of `k` as charged. Descent from that statement to a non-closed coefficient field is the same scalar-extension/faithful-flatness step already reviewed in the history stop, and is not re-litigated here.

---

## Promotion (restated)

**Accept `KUMMER NORMALIZATION SPLITS; FULL-CUBIC BOUNDARY REDUCTION TYPE-FAILS WITHOUT ORBIT DEGREE THREE; THE NORMALIZED CONSTANT-W SCHEME IS EXACTLY COMMON-CUBIC UNION ONE DAVENPORT--STOTHERS CURVE; HIGH SOURCE ROWS REDUCE TO FIVE COEFFICIENTS PLUS KAPPA; A PURE DS SOURCE PATH IS CONDITIONALLY EMPTY` at the stated scopes.**

**Do not promote this to** a polynomial Kummer depression, orbit degree three, filtered common-root persistence, derived pure-DS entry from the full `(6,9)` system, cube-mismatch closure, a solution of the lower Pfaffian/terminal rows, a `(6,9)` Keller pair or exclusion, or JC2.

**Smallest valid successor:** the four lower Pfaffian rows and the terminal Keller row of the five-variable-plus-`kappa` form, treated componentwise with the true minimal boundary factor, together with the independent cube-mismatch branch. No generic coefficient search, no AWS.

---

## Quarantine (restated)

No result here proves or disproves JC2. PASS strings are regression markers. Literature was source-checked only for historical claims actually used. The reviewed partial-`y` history stop licenses actual degrees `(6,9)` with `3\mid H` and leading powers `h^2,h^3`; it does not license a filtered common root, orbit degree three, polynomial depression, or nonlinear closure. Independent reconstruction, not the producer scripts, is the evidence for every numbered claim.
