# Hostile different-model review — GCD3 `(6,9)` lower-Pfaffian successor

| Field | Value |
|---|---|
| Claim under review | Frozen producer lower-Pfaffian successor: the four lower zero rows of the aligned nontrivial-Kummer `(6,9)` form integrate to four exact invariants whose reduced fibre is a zero-bracket sheet union an elliptic sheet; the terminal Keller row excludes both sheets in that branch |
| Overall verdict | **CONFIRMED** |
| Smallest failing identity | none |
| Smallest missing hypothesis | none that breaks a numbered claim (non-blocking: the registered Python replay inserts the first-gate `b`-polynomials and checks high-row vanishing rather than integrating the eight rows in-place; independent sequential integration recovered the same polynomials and the full eight-constant family) |
| Evidence tier | independent sequential integration of the eight high source rows; independent expansion of `D`, triangular exactness, weights, and all four potentials; second-engine Singular primary decomposition (`lp` order, both GTZ and SY) of the universal invariant ideal; independent polynomial pullback of the terminal one-form and rederivation of `beta`; independent DS bracket, both 5-row determinants (Berkowitz), descent, and every finite-place/infinity valuation; unmodified rerun of both registered replays as regression only |
| Reviewer / model | Grok 4.6 (xAI). Different model family from the producer (OpenAI Codex, GPT-5 family) |
| Repo | `/Users/dc/code/math/jc2` |
| Git HEAD | `1e4480c14f2ab9c4145eb6f6c74f0ac348baf76a` (matches the charged bank) |
| Review window (UTC) | 2026-08-24T14:21:13Z – 2026-08-24T14:38:03Z |
| Python | uv-pinned CPython 3.11.11 + SymPy `1.14.0` (registered replay and independent reconstruction) |
| Singular | `/opt/homebrew/bin/Singular` 4.4.1 |
| Host | `dc-mbp-m2.local`, Darwin arm64 |

Producer, freeze, and cited reviewed predecessor reread in full before any verdict:

- `xmodel/gcd3-69-lower-pfaffian-successor-20260824.md` (SHA-256 `7671785519bf4e55b602f117740bd8d8571c6982a8916235407a2bb0a2263043`)
- `cases/gcd3_69_lower_pfaffian_successor_20260824/MANIFEST.sha256` (SHA-256 `cff1e62028af45f81eb4f00ca72f65733d03a94dc95d29614c09139532c817b1`)
- `cases/gcd3_69_lower_pfaffian_successor_20260824/FREEZE.sha256` (SHA-256 `e48ba73639bf582409da246f4ee6f83add26a6b67528b329c691075d5f510874`)
- `xmodel/gcd3-69-common-cubic-first-gate-20260824.md` (SHA-256 `f63bf74fd1013c74645f9f7fe9292db69199572b390b5b19d160c5ed13b373e8`)
- `xmodel/gcd3-69-common-cubic-first-gate-review-grok-20260824.md` (SHA-256 `5416440bc12bb50ecebfdfa520082aa9e88a26069b43deb13bdaabfcd1690503`)

The committed basis is exactly `1e4480c14f2ab9c4145eb6f6c74f0ac348baf76a`. Named producer artifacts remain uncommitted on top of that basis. No producer, case, canonical, ladder, notes, prompt, log, or run file was edited. No enumerator, exponent rectangle, or AWS helper was written into the tree. Independent reconstruction lived only in `/tmp`.

The predecessor is consumed only at its reviewed scope: aligned nontrivial cubic Kummer, five moving coefficients plus essential `kappa`, historical `3\mid\deg(h)`, and the pure-DS valuation lemma. Full-cubic boundary divisibility, cube-core alignment, polynomiality of `z=sy+r`, and a general `(6,9)` exclusion are not imported. The producer does not import those either.

---

## Promotion

**Accept `THE FOUR LOWER ZERO ROWS INTEGRATE TO FOUR EXACT INVARIANTS WHOSE REDUCED FIBRE HAS ONLY A ZERO-BRACKET SHEET AND AN ELLIPTIC SHEET; THE TERMINAL KELLER ROW EXCLUDES BOTH SHEETS IN THE ALIGNED NONTRIVIAL-KUMMER BRANCH` at the stated scopes.**

Conditional on the frozen high-row normal form and the reviewed history input, the aligned nontrivial-Kummer `(6,9)` branch is empty. The argument uses no boundary reduction.

- The eight high rows reconstruct `g_0` and the essential deformation `kappa(z^3+(a_4/2)z+a_3/2)`. The chain rule is `J_{(x,y)}=sD` with `z_x` cancelling. Cube mismatch and aligned cube-core extra constants are not inputs.
- The four lower rows triangularise to exact first integrals `I_4,I_3,I_2,I_1` of Kummer weights `(1,2,0,1)`. Nonzero weights and the constant field of `L` force `I_4=I_3=I_1=0`, `I_2=\mu\in k`.
- Universally over `Q[a_0,\ldots,a_4,kappa,mu]`, the radical of those four equations is exactly `P_A\cap P_B`. These are the only minimal reduced primes. The displayed `P_E` is associated and contains `P_A` ideal-wise, so it is embedded in the zero-bracket sheet. An `L`-valued path has prime kernel and cannot switch reduced sheets.
- Sheet `P_A` is `f=K^2+d`, `g=K^3+(kappa+3d/2)K` with `d=w/4\in k`. Direct differentiation gives `D=0` for every moving `K` and every constant `d,kappa`, including nonzero values. The terminal row cannot occur.
- Sheet `P_B` is the elliptic curve `Y^2=3X^3+4096C` in Kummer-homogeneous coordinates of weights `(1,0,0)`. The polynomial terminal pullback is `(10)`; in the function field it is `beta=(7Y^2-12288C)\,dY/(147456X)` with this sign and factor. Then `X=sR` with `Y,R\in k(x)`, and `beta=j/s` yields both equations `(12)` and the cleared equation `(13)` with no lost factor of `s`, `3`, or `j`.
- For `C\neq 0`, constant `Y` makes `beta=0` before clearing (including `X\equiv 0` from the polynomial factors in `(10)`). A nonconstant rational `Y` is a surjective morphism `P^1\to P^1`; at least one of the two roots of `7Y^2-12288C` has a finite preimage `p`. At ramification index `e\geq 1` one has `Y(p)^2-4096C\neq 0`, `X(p)\neq 0`, and `ord_p(h)=3-6e<0`, contradicting that `h` is a polynomial and `p` is finite. Poles, ramification, `Y'=0`, infinity, and chart escape are separate and do not escape.
- For `C=0`, `EB=(3/4)X^2(X-3a_4^2)` without division. `X=0` lies on `P_A`. The other factor is the shifted Davenport–Stothers curve `f=f_\lambda-2kappa/3`, `g=g_\lambda`, with bracket `567\lambda^6` and five-row determinant `(3^{18}7/32)\lambda^{20}`. The terminal ODE descends to the predecessor's `(7.4)`. Every finite-place and infinity valuation of that ODE, including constant `h`, the cancelled case, `k\geq 1`, one-zero support, leading coefficient `-\sum k_i`, and `3\mid\deg(h)\Rightarrow 3\mid k`, makes `h` a cube and contradicts nontrivial Kummer. The constant subtraction changes none of this. `lambda=0`, isolated zeros, and every unshifted determinant factor in `(22)` are dispatched without inverting `M`.

**Do not promote this to:** emptiness of the cube-mismatch branch `delta\neq 0`; an aligned cube branch in which nontrivial Kummer weights do not kill the other high-row constants; a general `(6,9)` exclusion; a global landing theorem; a polynomial identity `z=sy+r`; a repair of the predecessor's full-cubic boundary `TYPE-FAIL`; a Keller pair of type `(6,9)`; or a JC2 decision.

**Smallest valid successor.** The cube-core high-row system, retaining `delta` and every weight-unforced integration constant. Do not open a generic coefficient rectangle or AWS. Do not relaunch the lower Pfaffian rows of the aligned nontrivial-Kummer form.

---

## Quarantine

No result here proves or disproves JC2, constructs or excludes a characteristic-zero Keller pair of type `(6,9)`, closes `delta\neq 0`, or kills aligned cube-core paths with unforced high-row constants. Producer strings `PASS-GCD3-69-LOWER-PFAFFIAN-SUCCESSOR` and `PASS-GCD3-69-LOWER-INVARIANT-DECOMPOSITION` were not used as evidence; the high-row connection, the four potentials, the universal primary decomposition, the terminal one-form, both sheets, both determinants, and the valuation lattice were re-derived. The predecessor is used only for the licensed high-row form, `3\mid\deg(h)`, and the pure-DS valuation lemma at its reviewed scope. Independent reconstruction, not the producer scripts, is the evidence for every numbered claim.

---

## Scope (not enlarged)

Exact identities and a provisional exclusion of the aligned nontrivial-Kummer `(6,9)` branch, conditional on the frozen high-row/history input, with no boundary reduction. Cube mismatch, aligned cube-core extra constants, arbitrary `(6,9)`, polynomial depression, orbit degree three, filtered persistence, and JC2 remain out of scope.

---

## Headline and subclaim table

| # | Exact subclaim | Verdict | What would have flipped it |
|---|---|---|---|
| 1 | Frozen hashes match. Conditional input is nontrivial cubic Kummer `L=k(x)(s)`, `s^3=h\in k[x]`, `3\mid\deg(h)`, the aligned depressed form with five moving `a_i` and constant `kappa`, and `J_{(x,y)}=sD`. Independent reconstruction of `g_0` from the eight high rows precedes any use of the five lower rows. Cube mismatch and aligned cube-core extra constants are not inputs | **CONFIRMED** | a frozen-hash mismatch; leftover `z_x` in the Jacobian; high-row `g_0` differing from the eight-row integral; `delta\neq 0` or extra `c_j` smuggled into the form |
| 2 | From undifferentiated `f,g`, the `z^4,\ldots,z^0` matrix, the four triangular corrections `(3)`, closedness/exactness, the formulas/normalisations for `I_4,I_3,I_2,I_1`, and weights `(1,2,0,1)` all hold. Derivatives vanish in that triangular order. The constant field of `L` licenses only `I_4=I_3=I_1=0`, `I_2=\mu\in k` | **CONFIRMED** | a non-closed corrected one-form; a different weight; an extra weight-zero invariant besides `I_2`; `I_4`-dot not equal to `[z^4]D` |
| 3 | Universally, `rad(I)=P_A\cap P_B` with exactly those two minimal reduced primes; displayed `P_E` is associated and `P_A\subset P_E` ideal-wise. Both reduced primes are geometrically integral. A prime kernel into `L` cannot switch reduced sheets | **CONFIRMED** | a third minimal prime; `rad(I)` properly containing `P_A\cap P_B`; `P_A` not contained in `P_E`; a reduced component that splits over `\overline Q`; an `L`-point whose kernel contains `P_A\cap P_B` but neither prime |
| 4 | `d=w/4\in k`, `mu=9d^2/4+3kappa d`, and `f=K^2+d`, `g=K^3+(kappa+3d/2)K`. Moving `K` and constant `d,kappa` give `D=0`, including nonzero `d` and `kappa`; the terminal row cannot occur | **CONFIRMED** | a nonzero source bracket on `(K^2+d,K^3+qK)`; `d` forced into a proper extension of `k`; nonzero `d` or `kappa` producing a nonzero terminal row |
| 5 | Polynomial pullback of the terminal one-form to `P_B` recovers both coefficients in `(10)`. Coordinates `X,Y,C` have weights `(1,0,0)` and satisfy `Y^2=3X^3+4096C`. Then `beta=(7Y^2-12288C)\,dY/(147456X)` with this sign and factor. `X=sR` with `Y,R\in k(x)`, and `beta=j/s` yields `(12)` and `(13)` with no lost factor of `s`, `3`, or `j` | **CONFIRMED** | a sign or factor error in `beta`; `wt(X)\neq 1`; a residual factor of `s` after cancelling `beta=j/s` against `X=sR`; cubing that dropped `j` or `3` |
| 6 | Constant `Y` is tested before clearing; `X\equiv 0` kills `beta` in `(10)` polynomially. Nonconstant rational `Y` is surjective on `P^1`; at least one forbidden finite value has a finite preimage. At ramification index `e`, both `Y^2-4096C` and `X` are nonzero and `ord(h)=3-6e<0`. Poles, ramification, `Y'=0`, infinity, and chart escape are separate | **CONFIRMED** | a constant-`Y` solution of `beta=j/s`; both forbidden values attained only at infinity for a nonconstant `Y`; `X(p)=0` at the chosen preimage; `ord(h)\geq 0` at that place; a ramified or `Y'=0` escape |
| 7 | `EB=(3/4)X^2(X-3a_4^2)` without division. `X=0` lies on the zero-bracket sheet. `X=3a_4^2`, `a_4=4lambda` is exactly `f=f_\lambda-2kappa/3`, `g=g_\lambda`. Bracket `567\lambda^6` and determinant `(3^{18}7/32)\lambda^{20}` hold. The terminal ODE descends to `(21)`. Every predecessor valuation, including constant `h`, cancellation, `k\geq 1`, one-zero support, leading coefficients, and `3\mid\deg(h)\Rightarrow 3\mid k`, makes `h` a cube. The constant subtraction changes none of it. `lambda=0`, isolated zeros, `(22)`, and every rank-zero stratum are dispatched without inverting `M` | **CONFIRMED** | a third `C=0` factor; `X=0` with nonzero bracket; shifted `g` retaining a `kappa` term; a lattice point of `5e+7n=1` with `e>0` and `2e+3n\neq 0` outside `k\geq 1`; cancelled valuation `0`; `r\geq 2` with vanishing leading coefficient; an extra invariant-fibre rank factor in `(22)` |
| 8 | Maximum promotion is the conditional exclusion of the aligned nontrivial-Kummer `(6,9)` branch under the reviewed high-row/history input, with no boundary reduction. It does not address `delta\neq 0`, aligned cube-core extra constants, arbitrary `(6,9)`, a global landing theorem, or JC2. The cube-core high-row system with every unforced constant is the smallest honest successor | **CONFIRMED** | a hidden use of full-cubic boundary reduction; promotion to a `(6,9)` or JC2 statement; a successor that drops `delta` or an unforced high-row constant |

All remarks below are non-blocking unless marked otherwise. None changes a numbered verdict.

---

## Replay and hashes

Frozen hashes, recomputed on the charged tree, match the launch prompt, `MANIFEST.sha256`, and `FREEZE.sha256`:

| Artifact | SHA-256 | Match |
|---|---|---|
| `xmodel/gcd3-69-lower-pfaffian-successor-20260824.md` | `7671785519bf4e55b602f117740bd8d8571c6982a8916235407a2bb0a2263043` | prompt, `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_lower_pfaffian_successor_20260824/MANIFEST.sha256` | `cff1e62028af45f81eb4f00ca72f65733d03a94dc95d29614c09139532c817b1` | prompt (self-hash) |
| `cases/gcd3_69_lower_pfaffian_successor_20260824/FREEZE.sha256` | `e48ba73639bf582409da246f4ee6f83add26a6b67528b329c691075d5f510874` | prompt (self-hash) |
| `cases/gcd3_69_lower_pfaffian_successor_20260824/PREREGISTRATION.md` | `8ad3c6aed3baa8cf1aba0d6ad9b337fdcca843501fdcb1832d1b7b5d0901d974` | `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_lower_pfaffian_successor_20260824/replay.py` | `55c5dddc5ae18b2fc26c6a39f29da20fbfb13c4e6afff439d69c5635c34afe19` | `MANIFEST`, `FREEZE` |
| `cases/gcd3_69_lower_pfaffian_successor_20260824/verify_lower_invariants.sing` | `557f3b33108dfc3279ad7699b796ea8a29eef673d3d162f144f6e655071391e6` | `MANIFEST`, `FREEZE` |
| `xmodel/gcd3-69-common-cubic-first-gate-20260824.md` | `f63bf74fd1013c74645f9f7fe9292db69199572b390b5b19d160c5ed13b373e8` | preregistration |
| `cases/gcd3_69_common_cubic_first_gate_20260824/replay.py` | `0ec1a7295cb9a3b090e1be2dfab1f730c12e2d8aeeec492c22932c9d720d3a94` | preregistration |
| `cases/gcd3_69_common_cubic_first_gate_20260824/verify_constant_w_scheme.sing` | `ea4761f641e1778bbc3cfa9f7769a9129ab1a3ca0ddd6d8944431400645eb06a` | preregistration |
| `cases/gcd3_69_common_cubic_first_gate_20260824/FREEZE.sha256` | `65370031b04014f96efc3ac814477a6689d5d5fef6b2695066ba6d60658ee585` | preregistration |
| `xmodel/gcd3-69-common-cubic-first-gate-review-grok-20260824.md` | `5416440bc12bb50ecebfdfa520082aa9e88a26069b43deb13bdaabfcd1690503` | reread predecessor review |

The case directory contains exactly those five files. No enumerator, exponent rectangle, or AWS helper is present.

Registered commands, rerun unmodified from the repository root:

```sh
uv run --offline --no-project --with sympy==1.14.0 python \
  cases/gcd3_69_lower_pfaffian_successor_20260824/replay.py

Singular -q \
  cases/gcd3_69_lower_pfaffian_successor_20260824/verify_lower_invariants.sing
```

Both exit 0. Exact output:

```text
PASS-GCD3-69-LOWER-PFAFFIAN-SUCCESSOR
lower_zero_rows=FOUR-TRIANGULAR-FIRST-INTEGRALS
kummer_constants=I4=I3=I1=0,I2=mu
reduced_invariant_strata=ZERO-BRACKET-SHEET,ELLIPTIC-SHEET
elliptic_terminal_beta=(7Y^2-12288C)dY/(147456X)
constant_Y=TERMINAL-FAILS-BEFORE-CLEARING
forbidden_finite_value=X-NONZERO-NO-CHART-ESCAPE
ramified_preimage=h-order=3-6e<0
elliptic_C_nonzero=POLYNOMIAL-H-VALUATION-EMPTY
elliptic_C_zero=ZERO-BRACKET-OR-SHIFTED-DS
component_switching=PRIME-GENERIC-PATH-CANNOT-SWITCH
embedded_C_zero=NO-EXTRA-FIELD-VALUED-BRANCH
denominator_rank_strata=DISPATCHED-WITHOUT-MATRIX-INVERSION
shifted_ds_bracket=567*lambda^6
shifted_ds_constant_subtraction=BRACKET-AND-VALUATIONS-UNCHANGED
aligned_noncube_69_branch=PROVISIONAL-EMPTY
full_cubic_boundary_reduction=UNUSED
cube_mismatch_branch=OPEN
jc2_inference=false

PASS-GCD3-69-LOWER-INVARIANT-DECOMPOSITION
minimal_reduced_components=ZERO-BRACKET-SHEET,ELLIPTIC-SHEET
embedded_C_zero_component=CONTAINED-IN-ZERO-BRACKET-SHEET
special_C_zero=ZERO-BRACKET-OR-SHIFTED-DS
```

Those PASS strings are regression only. The independent reconstruction of Claims 1–7 is the evidence.

Independent reconstruction, second derivation or second engine for every load-bearing finite identity: sequential high-row integration and four-potential exactness in SymPy on a solver path that does not import producer formulas; Berkowitz determinants; graph isomorphisms for geometric primeness; Singular primary decomposition in monomial order `lp` (producer used `dp`) by both GTZ and SY. Both algorithms return exactly three associated primes, identified with `P_A`, `P_E`, `P_B`; `minAss` has size two; `radical(I)=P_A\cap P_B`; `P_A\subset P_E`; the `P_A` and `P_B` primaries equal their primes; the `P_E` primary is properly contained in `P_E`.

---

## Claim 1 — input perimeter and source bracket

**CONFIRMED.**

Every frozen hash above matches the launch prompt, `MANIFEST`, and `FREEZE`. Git `HEAD` is the charged bank `1e4480c14f2ab9c4145eb6f6c74f0ac348baf76a`. The preregistration's predecessor package matches the reread first-gate freeze.

The charged input is exactly the aligned nontrivial-Kummer branch of the reviewed first gate: `F=k(x)`, `L=F(s)`, `s^3=h\in k[x]`, `L/F` cubic Kummer, `3\mid\deg(h)`, and the depressed path

```text
f=z^6+a4 z^4+a3 z^3+a2 z^2+a1 z+a0,
g=g0(a)+kappa(z^3+(a4/2)z+a3/2),
```

with `kappa` constant. Cube-core mismatch `delta\neq 0` and the extra high-row constants that survive only when Kummer is trivial are not present in this form and are not used below.

Chain rule, including `x`-dependence of `s` and `r` in `z=sy+r`:

```text
P_x=f_x+f_z z_x,   Q_x=g_x+g_z z_x,   P_y=s f_z,   Q_y=s g_z,
J_{(x,y)}=s(f_x g_z-f_z g_x)=s D.
```

The `z_x` terms cancel in the determinant. Thus `[z^4]D=\cdots=[z]D=0` are the four lower zero rows and `[z^0]D=j/s` is the terminal row, with `j\in k^*`. No polynomial boundary value is consumed.

Independent sequential integration of the eight high rows `z^{12},\ldots,z^5`, before any lower-row matrix, recovers the full eight-constant connection. The top two steps are `b_7=3a_4/2+c_7`, `b_6=3a_3/2+c_6`; continuing downward reproduces the first-gate formulae including the `c_7,c_6,c_5` terms of `(1.9)`, and at vanishing constants the zero-constant solution

```text
b7=3 a4/2,
b6=3 a3/2,
b5=3(4a2+a4^2)/8,
b4=3(2a1+a3 a4)/4,
b3=(24 a0+12 a2 a4+6 a3^2-a4^3)/16,
b2=3(4 a1 a4+4 a2 a3-a3 a4^2)/16,
b1=3(32 a0 a4+32 a1 a3+16 a2^2-8 a2 a4^2-8 a3^2 a4+a4^4)/128,
b0=(24 a0 a3+24 a1 a2-6 a1 a4^2-12 a2 a3 a4-2 a3^3+3 a3 a4^3)/32.
```

Kummer weights `wt(c_j)\equiv -j\pmod{3}` kill `c_7,c_5,c_4,c_2,c_1`. Target shear and translation remove `c_6,c_0`. The remaining constant is `kappa=c_3`, and substituting the `c_3`-family into `g` equals `g_0+kappa(z^3+(a_4/2)z+a_3/2)` identically. After this substitution the rows `z^{12},\ldots,z^5` of `D` vanish identically in the `a`-velocities. Cube-mismatch `delta` and the killed `c_j` never re-enter.

No identity failed.

---

## Claim 2 — four first integrals and Kummer constants

**CONFIRMED.**

From the undifferentiated pair `(f,g)` just reconstructed, `D` is linear in `da_0,\ldots,da_4`. The five lower coefficient rows are the matrix with rows `[z^4],\ldots,[z^0]` and columns `da_0,\ldots,da_4`. Direct curls:

- `alpha_4` and `alpha_3` are already closed, hence exact;
- `alpha_2` is not closed, and `alpha_2-(a_4/2)alpha_4` is closed, while the nearby correction `(a_4/3)alpha_4` is not;
- `alpha_1` is not closed, and `alpha_1-(a_3/3)alpha_4-(a_4/3)alpha_3` is closed, while the nearby correction with denominators `2` is not.

Integration of the four closed forms recovers potentials whose exterior derivatives are exactly `(3)`. Differentiating those potentials back along a path therefore gives

```text
I4-dot = [z^4]D,
I3-dot = [z^3]D,
I2-dot = [z^2]D-(a4/2)[z^4]D,
I1-dot = [z]D-(a3/3)[z^4]D-(a4/3)[z^3]D.
```

The four lower zero rows therefore kill the four `I`-derivatives in that triangular order: `I_4` and `I_3` each vanish with a single row; `I_2` needs `[z^4]` and `[z^2]`; `I_1` needs `[z^4]`, `[z^3]`, and `[z]`.

Writing `A=4a_2-a_4^2`, `B=2a_1-a_3 a_4`, and taking `e_4,e_3` as in the producer, the independently integrated potentials satisfy

```text
I4=9 e4/128 + 3 kappa A/4,     I3=9 e3/128 + 3 kappa B/2,
I2=N2/512,                     I1=-N1/128,
```

with `N_2` and `N_1` exactly the displayed polynomials (the comparison is after integration, not an imported ansatz). Coefficient weights of `(a_0,a_1,a_2,a_3,a_4,kappa)` are `(0,2,1,0,2,0)\pmod{3}`, and every monomial of `(I_4,I_3,I_2,I_1)` is homogeneous of weights `(1,2,0,1)`.

All four `I`'s are therefore `x`-constants along solutions of the four lower rows. The constant field of the finite extension `L/k(x)` is `k` (`k` algebraically closed, as charged). A weight-`1` or weight-`2` constant is multiplied by a nontrivial cube root of unity under `sigma(s)=omega s`, hence vanishes; a weight-`0` constant is Galois-invariant, lies in `k(x)`, and being `x`-constant lies in `k`. This licenses only

```text
I4=I3=I1=0,          I2=mu in k.
```

No extra weight-zero invariant appears. No identity failed.

---

## Claim 3 — universal invariant-fibre decomposition

**CONFIRMED.**  No missing component is frozen.

Generators were rebuilt from the independently integrated `I`'s (clearing denominators: `p_4=(128/3)I_4`, `p_3=(128/3)I_3`, `p_2=512(I_2-mu)`, `p_1=-128 I_1`) and decomposed in the ring `Q[a_0,a_1,a_2,a_3,a_4,k,m]` with monomial order `lp`, opposite to the producer’s `dp`. Both `primdecGTZ` and `primdecSY` return three associated primes, identified by two-sided reduction with the displayed ideals

```text
PA=(A, B, 9w^2+48 k w-64 m),
PB=(a3, a1, EB, 48 a0-12 a2 a4+3 a4^3+32 k),
PE=(C, A, B, 12 a0-3 a3^2+8 k).
```

`minAssGTZ` has size two. `radical(I)` equals `P_A\cap P_B` by two-sided reduction. `P_A` reduces to zero modulo `P_E`, so `P_A\subset P_E` ideal-wise and `V(P_E)\subset V(P_A)`. The `P_A` and `P_B` primaries equal their primes (reduced components). The `P_E` primary is properly contained in `P_E` (four leftover prime generators), so `P_E` is embedded and the original scheme is nonreduced along that locus. Dimensions: `dim P_A=4`, `dim P_B=3`, `dim P_E=3` in the seven-space `(a_0,\ldots,a_4,k,m)`.

Geometric primeness does not rest on a sampled fibre. After eliminating the graph variables, `elim(P_A,a_1 a_2 m)=(0)` and `elim(P_B,a_0 a_1 a_3 m)=(0)`. Explicitly: `P_A` is the graph

```text
a2=a4^2/4,   a1=a3 a4/2,   m=(9w^2+48 k w)/64
```

over affine four-space in `(a_0,a_3,a_4,k)`; `P_B` is the graph

```text
a1=a3=0,   a0=a2 a4/4-a4^3/16-2k/3,
m=-k^2-(384 a2^3-432 a2^2 a4^2+144 a2 a4^4-15 a4^6)/1024
```

over affine three-space in `(a_2,a_4,k)`; `P_E` is the graph `A=B=0`, `m=-k^2`, `a_0=(3a_3^2-8k)/12` over `(a_3,a_4,k)`. Each quotient is a polynomial ring over `Q`, hence a domain after every extension of `Q`. Both reduced primes are geometrically integral.

A coefficient path is a homomorphism `Q[a_0,\ldots,a_4,k,m]\to L`. Its kernel is prime, hence radical, and contains `I`, therefore contains `rad(I)=P_A\cap P_B`. A prime containing an intersection of two primes contains one of them. The path, as an `L`-valued point, lies on `P_A` or on `P_B` (or on their intersection). It cannot occupy one reduced sheet at a generic `x` and the other at a special `x`: the `a_i` are elements of the field `L`, not a family of specialisations. A kernel equal to a prime of the intersection still lands in `V(P_A)\cap V(P_B)\subset V(P_A)`, which is the zero-bracket locus treated in Claim 4. Nilpotent structure on the embedded component `P_E` cannot map nontrivially to a field.

No identity failed. No missing reduced component or specialisation is frozen.

---

## Claim 4 — zero-bracket sheet `P_A`

**CONFIRMED.**

On `P_A`, `A=B=0` give `a_2=a_4^2/4` and `a_1=a_3 a_4/2`. Put `K=z^3+(a_4/2)z+a_3/2` and `d=w/4` with `w=4a_0-a_3^2`. Then `f=K^2+d` and, using the reconstructed `g`,

```text
g=K^3+(kappa+3d/2)K.
```

The remaining generator of `P_A` is `9w^2+48 kappa w-64 mu=0`, i.e.

```text
mu=9d^2/4+3 kappa d.
```

This is quadratic in `d` with coefficients in `k`, so `d` is algebraic over `k` and therefore lies in `k`. Independently, `I_4=I_3=I_1` vanish on this substitution and `I_2` evaluates to `9d^2/4+3 kappa d`.

For moving `K` (velocities of the two coefficients of `K`) and constant `d,kappa`, put `q=kappa+3d/2`. Then

```text
D=(2 K K_vel) * d(K^3+q K)/dz - d(K^2+d)/dz * (3K^2+q) K_vel
 =(2K)(3K^2+q) K_z K_vel - (2K K_z)(3K^2+q) K_vel
 =0.
```

The cancellation is an algebraic tautology and does not use `d=0` or `kappa=0`. Substituting nonzero constants (`d=5`, `kappa=7`) leaves `D=0`. Thus every path on `P_A` has identically vanishing source bracket, so `[z^0]D=0\neq j/s`. The nonzero terminal row cannot occur on this reduced sheet, including the pure common-power point `d=kappa=0`, the essential high-row deformation `kappa K`, and the further lower-row constant `d`. They remain one reduced zero-bracket sheet, not a silent identification with Davenport–Stothers.

No identity failed.

---

## Claim 5 — elliptic sheet and terminal orientation

**CONFIRMED.**

On `P_B` one has `a_3=a_1=0` and

```text
a0=a2 a4/4 - a4^3/16 - 2 kappa/3.
```

Then `I_4=I_3=I_1` vanish, and `I_2-mu=-EB/1024`. The Kummer-homogeneous coordinates `X=8a_2-2a_4^2`, `Y=3a_4 X`, `C=kappa^2+mu` have weights `wt(X)=1` and `wt(Y)=wt(C)=0`, computed from the monomials, and satisfy

```text
Y^2-3X^3-4096 C = -4 EB.
```

On `P_B` this is `Y^2=3X^3+4096C`. Because `wt(X)=1`, `sigma(X)=omega X`, so `X/s` is Galois-invariant in `L` and therefore lies in `k(x)`: `X=sR` with `R\in k(x)`. Because `wt(Y)=0`, `Y\in k(x)`.

The terminal row `alpha_0` is pulled back to `P_B` before any division: `da_1=da_3=0` and `da_0=d(a_{0,B})`. The resulting coefficients of `da_4` and `da_2` factor as

```text
beta_a4=3(4a2-3a4^2)(4a2-a4^2)(4a2+a4^2)/2048,
beta_a2=3 a4 (4a2-a4^2)(4a2+a4^2)/512.
```

Changing to `(a_4,X)` and then to `(X,Y)` via `dY=3X\,da_4+3a_4\,dX`, the coefficient of `dY` on the chart `X\neq 0`, after eliminating `mu` by the curve, is independently

```text
qY=(7Y^2-12288 C)/(147456 X).
```

The same identity is the statement that `beta_A=qY\cdot 3X` and `beta_X=qY\cdot 3a_4` on the curve. The sign and the factor `147456=2^{14}3^2` are therefore those of the polynomial pullback, not of a later normalisation.

The terminal equation `beta=j/s` is, for nonconstant `Y`,

```text
(7Y^2-12288 C) Y'/(147456 X)=j/s.
```

Substituting `X=sR` cancels exactly one factor of `s` against the right-hand side and leaves

```text
(7Y^2-12288 C) Y'=147456 j R,
```

valid wherever `R\neq 0` (i.e. wherever `X\neq 0`, treated in Claim 6). The curve identity with `X=sR` and `s^3=h` is

```text
3 h R^3=3 X^3=Y^2-4096 C
```

on `P_B`. Cubing the first equation of `(12)` and substituting into the second produces `(13)` as an identity in `k(x)`: the factor `3` on the left is kept, `(147456 j)^3` appears from clearing the cube of the denominator, and `j\in k^*` is not identically zero. No residual factor of `s` remains after the single cancellation above.

No identity failed.

---

## Claim 6 — `C\neq 0` and every no-loss case

**CONFIRMED.**  No valuation case was omitted; no counterexample is frozen.

Constant `Y` is tested against `beta=j/s` before any clearing or cubing. If `X\equiv 0`, both polynomial factors `(4a_2-a_4^2)` in `(10)` vanish, so `beta_a4=beta_a2=0`. If `X\not\equiv 0`, then `dY=0` in the function field and `(11)` gives `beta=0`. Either way `beta=0\neq j/s`. (On `C\neq 0` the curve moreover forbids `X\equiv 0`, because `Y=3a_4 X=0` would force `4096C=0`.) No constant solution is introduced or lost by `(13)`.

Now `C\neq 0` and `Y` nonconstant. Then `Y\in k(x)` is a nonconstant morphism `P^1\to P^1`. Over algebraically closed `k` every such morphism is surjective. The two roots of `7Y^2-12288C` are

```text
y_plus=-y_minus,     y_plus^2=12288 C/7 \neq 0,
```

hence distinct. The single source point at infinity attains at most one of these two finite values, so at least one has a finite preimage `p`. (If `Y(\infty)=y_+`, then `Y-y_+` may have no finite zero — e.g. `Y=y_++1/x` — but `y_-\neq y_+` then has only finite preimages.)

At such a `p`, write `ord_p(Y-y_+)=e\geq 1`. Then `Y+y_+=2y_+\neq 0`, so

```text
ord_p(7Y^2-12288 C)=e,        ord_p(Y')=e-1
```

in characteristic zero. This includes every ramified preimage: `Y'=0` is exactly `e\geq 2` and only increases `e`. Direct substitution of the forbidden value gives

```text
Y(p)^2-4096 C=-16384 C/7 \neq 0,
X(p)^3=-16384 C/21 \neq 0.
```

Thus `p` is not a pole of `Y`, not a zero of `X`, and not an affine-chart escape of `(11)`. In particular `h(p)R(p)^3\neq 0`. Equation `(13)` is an identity in `k(x)` for this nonconstant non-`C=0` locus (`7Y^2-12288C` is not identically zero, else `Y` would be constant). Taking `ord_p` of both sides,

```text
ord_p(h)+3e+3(e-1)=0,
ord_p(h)=3-6e<0.
```

But `h` is a polynomial and `p` is finite, so `ord_p(h)\geq 0`. This contradiction excludes the entire `C\neq 0` sheet, including ramified and `Y'=0` points. Poles of `Y` are not the chosen `p`. Infinity was used only to guarantee a finite preimage of at least one forbidden value, and is not itself the contradiction point. The identity `(13)` is not invoked at a generic unramified point in place of this argument.

No identity failed.

---

## Claim 7 — `C=0`, shifted DS, and all rank loci

**CONFIRMED.**  No valuation case was omitted; no counterexample is frozen.

Without division, `EB` at `mu=-kappa^2` factors as

```text
EB=(3/4) X^2 (X-3 a4^2)=3(4a2-a4^2)^2 (8a2-5a4^2).
```

The source target is a field, so there are two cases.

If `X=0`, then `a_2=a_4^2/4`, `a_0=-2kappa/3`, and

```text
f=K0^2-2kappa/3,     g=K0^3,     K0=z^3+(a4/2)z,
```

which is the `P_A` substitution with `d=-2kappa/3` and `v=0`. Its bracket vanishes by Claim 4, and `mu=9d^2/4+3kappa d=-kappa^2` is consistent with `C=0`.

If `X=3a_4^2`, put `a_4=4lambda`. Then `a_2=10lambda^2`, `a_3=a_1=0`, `a_0=6lambda^3-2kappa/3`, `mu=-kappa^2`, and

```text
f=f_lambda-2kappa/3,     g=g_lambda,
```

with `f_lambda,g_lambda` the first-gate Davenport–Stothers pair. The `kappa K` deformation is cancelled by the `a_0`-dependence of `g_0`: `g` equals `g_lambda` with no residual `kappa` term. The constant `-2kappa/3` has zero `lambda` and `z` derivatives, so the source bracket equals the unshifted bracket. Direct expansion and weighted Euler `2lambda J_{(lambda,z)}=3W` with `W=378 lambda^7` both give

```text
J_{(lambda,z)}=567 lambda^6.
```

The five-row matrix of `D` on this path has, by an independent Berkowitz determinant,

```text
det M=(3^{18} 7/32) lambda^{20}=2711943423 lambda^{20}/32.
```

For `lambda\neq 0` there is no rank loss. The terminal equation is the contraction of `alpha_0` along the path, i.e. `s\cdot 567 lambda^6 lambda'=j`, exactly `(20)`. The weight of `lambda` is two, so `lambda=s^2 q` with `q\in k(x)`. Direct expansion

```text
s lambda^6 lambda' = h^4 (2/3) h' q^7 + h^5 q^6 q'
```

converts `(20)` into `(21)`:

```text
189 h^4 q^6 (2 h' q + 3 h q')=j.
```

This is the predecessor’s `(7.4)`. The constant subtraction is invisible to `(18)` and to `(20)`–`(21)`.

Finite places, re-audited rather than quoted. Write `e=v(h)\geq 0`, `n=v(q)`, local parameter `t`. Leading terms of the combination are `CD t^{e+n-1}(2e+3n)`, so cancellation occurs if and only if `2e+3n=0`.

- If `e=0` and `n\neq 0`, the `h q'` term has valuation `n-1` and total valuation `7n-1=0` is impossible in integers. Thus `e=0` forces `n=0` at that place.
- If `e>0` and `n=0`, then `v(2h'q)=e-1<e\leq v(3h q')`, no cancellation, and `5e-1=0` is impossible.
- If `e>0`, `n\neq 0`, and `2e+3n\neq 0`, constancy forces `5e+7n-1=0`. Every integer solution is `e=3+7k`, `n=-2-5k`. The conditions `e>0` and non-cancellation exclude `k\leq 0` (`k=0` is precisely `2e+3n=0`; `k\leq -1` has `e\leq -4`, a pole of the polynomial `h`). Thus `k\geq 1` and `2e+3n=-k\neq 0`.
- If `2e+3n=0` with `e>0`, then `n=-2e/3` and `v(h^4 q^6)=0`, but `v(2h'q+3h q')\geq e+n=e/3>0`. Pure monomials `h=C t^3`, `q=D t^{-2}` make the combination identically zero. The unit perturbation `h=C t^3(1+c_1 t)`, `q=D t^{-2}(1+d_1 t)` expands to `CD\bigl((3d_1+2c_1)t+5 c_1 d_1 t^2\bigr)`, valuation exactly `1`. In every subcase the left-hand side of `(21)` vanishes at the place and cannot be a nonzero constant.

Hence the divisor of `q` is supported exactly on the zeros of `h`. If `h` has no zero then `h` and `q` are both constant, the left-hand side of `(21)` is identically zero, and `j\neq 0` is contradicted. Thus `h` has `r\geq 1` distinct zeros.

Infinity, re-audited. With `d=\deg(h)=3r+7\sum k_i` and `v_\infty(q)=2r+5\sum k_i`,

```text
2h'q+3h q' \sim C D (2d-3(2r+5\sum k_i)) x^{d-1-2r-5\sum k_i}
           = C D (-\sum k_i) x^{r+2\sum k_i-1}.
```

The leading coefficient contains `-\sum k_i\neq 0` because each `k_i\geq 1`. The full left-hand side of `(21)` therefore has `v_\infty=1-r`. Constancy forces `r=1`. Thus `h=C(x-a)^{3+7k}`. The reviewed historical residue `3\mid\deg(h)` forces `3\mid k`. Writing `k=3ell` with `ell\geq 1` yields `e=3+21ell`, so `h` is a cube in `k[x]`. This contradicts the nontrivial-Kummer hypothesis of the branch under review. (The predecessor’s further polynomial-boundary killing of the remaining cube case is not used, and is not needed, because a cube core is already outside this branch.)

At `lambda\equiv 0` the bracket `(18)` vanishes, so the terminal row cannot be `j/s`. If `lambda` is not identically zero, isolated zeros are already classified by the rational identity `(21)=j\neq 0`: an extra finite zero of `lambda` would be a place with `e=0` and `n>0`, excluded above. The rank-zero locus `lambda=0` of `(19)` is therefore not an unexamined source trajectory.

Negative control: the unshifted static substitution `a_0=6lambda^3` has, by a second Berkowitz determinant,

```text
det M=(81/32) lambda^5 (4 kappa+63 lambda^3) (8 kappa^2-72 kappa lambda^3+729 lambda^6)^2,
```

and `I_4=18 kappa lambda^2`. On the Kummer invariant fibre with `lambda\neq 0` this first forces `kappa=0`, after which both extra factors are `63 lambda^3` and `729 lambda^6`, nonzero. At `lambda=0` the bracket is zero. None of the apparent extra rank factors discarded by a generic matrix solve is a surviving invariant-fibre path. The correct `C=0` path is the shifted curve, not the unshifted ansatz. The proof never inverts `M`.

No identity failed.

---

## Claim 8 — exact promotion and quarantine

**CONFIRMED.**

The maximum licensed promotion is exactly the list in the prompt and in producer §7: a conditional exclusion of the aligned nontrivial-Kummer `(6,9)` branch under the reviewed high-row/history input, using no boundary reduction. The gate does not address the live `delta\neq 0` cube-mismatch branch; aligned cube branches for which nontrivial Kummer weights do not kill the other high-row integration constants; arbitrary degree-`(6,9)` pairs outside the frozen normal form; a global landing theorem; or JC2. It does not repair or invoke the predecessor’s chosen-root/full-cubic `TYPE-FAIL`. It does not claim polynomiality of `z=sy+r`.

The smallest honest successor is the cube-core high-row system, retaining `delta` and every weight-unforced integration constant. That package is the complement of the nontrivial-Kummer reduction already used: when `h` is a cube there is no weight action to kill `c_7,c_5,c_4,c_2,c_1`, and when `delta\neq 0` the depressions do not align. The two fragments may be sequenced internally, but dropping either would leave a live cube-core residue. A generic coefficient rectangle and AWS remain unlicensed. The lower Pfaffian rows of the aligned nontrivial-Kummer form have been discharged and must not be relaunched.

No identity failed.

---

## Non-blocking remarks

1. The associated prime `P_E` is the reduced support of a nonreduced primary (`P_E` has four leftover generators modulo that primary). The producer classifies field-valued branches by the two reduced primes, which is the correct statement: a homomorphism to the field `L` has radical kernel and cannot see nilpotents.
2. Dimensions `dim P_A=4` and `dim P_B=3` are computed in the seven-space that includes the auxiliary constants `(kappa,mu)`. They are consistent with the graph presentations above.
3. Surjectivity of a nonconstant `Y:P^1\to P^1` uses algebraic closure of `k` as charged. Descent from that statement to a non-closed coefficient field is the same scalar-extension step already reviewed in the history stop, and is not re-litigated here.
4. Emptiness of the noncube shifted-DS branch is the arithmetic `3\mid\deg(h)\Rightarrow 3\mid k`, inherited from the reviewed predecessor, not a claim that `5e+7n=1` has no noncube lattice points. Without `3\mid H` the point `k\not\equiv 0\pmod{3}` would be a noncube ODE solution in `L`; those pairs are already outside the licensed residue.
5. A sign error in `beta` would have survived cubing as `A=-B` in `(13)` and would still have forced `ord_p(h)=3-6e<0`. The sign was nevertheless rederived from the polynomial pullback before cubing, and matches `(11)`.
6. The registered Python replay inserts the first-gate `b`-polynomials and asserts high-row vanishing, rather than integrating the eight rows in-place. Independent sequential integration recovered those polynomials and the full eight-constant family. This is a replay shortcut, not a hole in the claim.

---

## Promotion (restated)

**Accept `THE FOUR LOWER ZERO ROWS INTEGRATE TO FOUR EXACT INVARIANTS WHOSE REDUCED FIBRE HAS ONLY A ZERO-BRACKET SHEET AND AN ELLIPTIC SHEET; THE TERMINAL KELLER ROW EXCLUDES BOTH SHEETS IN THE ALIGNED NONTRIVIAL-KUMMER BRANCH` at the stated scopes.**

**Do not promote this to** emptiness of `delta\neq 0`, an aligned cube branch with weight-unforced high-row constants, a general `(6,9)` exclusion, a global landing theorem, a polynomial Kummer depression, a repair of full-cubic boundary reduction, a Keller pair of type `(6,9)`, or JC2.

**Smallest valid successor:** the cube-core high-row system, retaining `delta` and every weight-unforced integration constant. No generic coefficient search, no AWS.

---

## Quarantine (restated)

No result here proves or disproves JC2. PASS strings are regression markers. The predecessor licenses actual degrees `(6,9)` with `3\mid\deg(h)` and the aligned five-plus-`kappa` form; it does not license cube-core extra constants, polynomial depression, orbit degree three, or nonlinear closure. Independent reconstruction, not the producer scripts, is the evidence for every numbered claim.
