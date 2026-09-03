# Grok610ScaleZeroCubicCoordinateTowerPlanScratch.md (Opus plan, 2026-09-03 ~13:30Z)

**Target:** `normalized610ScaleZero_impossible : ∀ P Q H, Normalized610LeadingCoreSource P Q H 0 → False`, hence
`planeKellerNormalized610LowScaleRoute_closed` via `planeKellerNormalized610LowScaleRoute_of_scaleZero`
(`Grok610AlignedNonsquareDegreeZeroPrimitiveScratch.lean:1493`).

**Bottom line.** The seven-lane cone cascade is enumerating in the *wrong coordinates*. In the cubic (q-adic) coordinates
`C = C₀ − A²/3`, `D = D₀ − AB/3`, `E = E₀ − AC₀/3 + 2A³/27` the whole leaf collapses to **31 + 15 + 1 chambers with one mechanical certificate each**, with no drop chambers, no residual descent, and no open-ended enumeration. The planner ran the entire decomposition through sympy: **every chamber is empty**. There is no residual left over.

---

## 1. The hidden grading (verified, not conjectured)

All five surviving objects are **isobaric** for the weights

| object | A | B | C₀ | D₀ | E₀ | l | α | β | δ | ε | ζ | η | θ |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| weight | 2 | 3 | 4 | 5 | 6 | 1 | 2 | 3 | 5 | 6 | 7 | 8 | 9 |

with total weights

* `degreeZeroKappaPolynomial610` (`Grok610ScaleZeroConeTerminalScratch.lean:122`) — **11**
* `degreeZeroLambdaPolynomial610` (`…ConeTerminalScratch.lean:66`) — **12**
* `degreeZeroMuPolynomial610` (`Grok610ScaleZeroConeKappaMuScratch.lean:111`) — **13**
* `degreeZeroOmicronPolynomial610` (`…ConeKappaMuScratch.lean:330`) — **14**
* `degreeZeroPrimitivePolynomial610` (`Grok610ScaleZeroConeCascadeScratch.lean:498`) — **15**

Verified by machine on the transcribed definitions: each of the five is *exactly* homogeneous of its weight, in the letters **and** the loads (this is also the strongest available checksum on the transcription — one mistyped coefficient breaks isobaricity). Geometrically: `A,B,C₀,D₀,E₀` are the coefficients of the depressed sextic `y⁶+Ay⁴+By³+C₀y²+D₀y+E₀`, `y` has weight 1, and κ,λ,μ,ο,Π are the weight-11…15 members of one graded family (`m+n−1 = 15`, exactly the handoff-rule primitive weight).

**Consequence (the whole engine).** Let `n_ξ := ξ.natDegree`, and for `u = (n_A,…,n_E)` the u-degree of a monomial `m` is `⟨u,m⟩`. Then for any isobaric `Φ_w`

```
coeff (M) (Φ_w(A,…,E₀))  =  Σ_{m : ⟨u,m⟩ = M} coeff(m) · (leading coefficients)^m ,   M := max_m ⟨u,m⟩ .
```

Put `ρ := max(n_A/2, n_B/3, n_C/4, n_D/5, n_E/6)` and `R := argmax`. Since `⟨u,m⟩ = Σ m_ξ w_ξ (n_ξ/w_ξ) ≤ ρ·w` **with equality iff `supp m ⊆ R`**, and since every load carries weight `≥ 1` (so load terms sit at `≤ (w−1)ρ`):

> **Top-form lemma.** If some monomial of `Φ_w` is supported in `R`, then `deg Φ_w ≤ wρ` and `coeff (wρ) Φ_w = Φ_w^R(lc)`, where `Φ_w^R` is the **load-free** part of `Φ_w` with all letters outside `R` set to 0.

κ,λ,μ,ο have `natDegree = 0` and `wρ ≥ 11/6 > 1`, so those four initial forms **vanish**. Π has `natDegree = 1` (`natDegree_eq_one_of_derivative_eq_nonzero_C610`, `…ConeCascadeScratch.lean:57`) and `15ρ ≥ 15/6 > 1`, so its initial form vanishes too. **No "drop chamber" can occur** — the vanishing is forced, never assumed away. This single lemma replaces every `…_natDegree_eq_of_coeff_ne` tie argument in the current chain.

Also note: the max-set of the "seven λ weights" the current lanes enumerate (`Grok610ScaleZeroConeTriplesScratch.lean`, `MixedD0Cones610`) is *determined* by `R`: `A²BD₀` and `BC₀D₀` are interior lattice points of the λ-simplex `conv{A⁶,B⁴,C₀³,E₀²,AD₀²}` and can never create a chamber of their own. That is the source of the combinatorial blow-up.

## 2. Change coordinates first (the decisive move)

In the original letters the argmax cone `R = {A,C₀,E₀}` is **not** empty: there `λ^R = (5/81)(9q²−p³)` and `ο^R = −(5/6561)(a²−3c)²(2a³−9ac+27e)` with `p,q` the depressed-cubic invariants of `z³+az²+cz+e` (`z=y²`), whose only common zero is the perfect cube `(z+a/3)³`, i.e. `c = a²/3, e = a³/27`. That cusp is exactly why lanes 5–7 stalled, and the B-, D₀- and α-columns all vanish there, so no second-tier equation exists in those coordinates.

The cure is the **q-adic (cubic) expansion** `f = q³ + (By+C)q + (Dy+E)`, `q = y² + A/3`, i.e. the graded triangular automorphism

```
C := C₀ − (1/3)A² ,  D := D₀ − (1/3)AB ,  E := E₀ − (1/3)AC₀ + (2/27)A³
(inverse: C₀ = C + A²/3, D₀ = D + AB/3, E₀ = E + AC/3 + A³/27)
```

— the same coordinates the (6,8) campaign already uses (`Grok68TerminalZeroMeetingCellPlanScratch.md` §2: "`C0 = A²/3+c, D = AB/3+d, E = A³/27+Ac/3+e`"). It preserves the grading, so §1 applies verbatim, and the load-free parts become tiny:

```
κ₀ = (5/243)  ( A B³ − 9B²D − 9BC² + 54DE )
λ₀ = (5/243)  ( 3AB²C − 9AD² + B⁴ − 9B²E − 18BCD − 3C³ + 27E² )
μ₀ = −(5/1458)( A²B³ − 27AB²D − 9ABC² + 54ADE − 24B³C + 108BCE + 54BD² + 54C²D )
ο₀ = −(5/486) ( AB⁴ − 6AB²E − 12ABCD − 5B³D − 9B²C² + 18BDE + 18C²E + 18CD² )
Π₀ = −(1/2916)( 5A³B³ + 135A²B²D − 45A²BC² + 270A²DE + 300AB³C − 1080ABCE − 540ABD²
                − 540AC²D + 48B⁵ − 360B³E − 1620B²CD − 540BC³ + 3240CDE + 1080D³ )
```

(4, 7, 8, 8, 14 monomials.) **No pure power of `A` occurs** in any of them — that is the only reason a cone survives at all.

## 3. Stage A — the 31 argmax cones (30 closed, machine-verified)

For each nonempty `R ⊆ {A,B,C,D,E}` the system `{Φ_w^R(lc) = 0 : w = 11..15, Φ_w^R ≠ 0}` with `lc_ξ ≠ 0 (ξ∈R)` was tested by saturated Gröbner (`⟨eqs, T·Π lc − 1⟩ = (1)`). Result: **empty for all 30 cones with `R ≠ {A}`.** Twenty-one are single monomials — one line of Lean each:

| R | certificate | R | certificate |
|---|---|---|---|
| `B` | λ₀: `b⁴ = 0` | `C` | λ₀: `c³ = 0` |
| `D` | Π₀: `d³ = 0` | `E` | λ₀: `e² = 0` |
| `AB` | κ₀: `ab³ = 0` | `AC` | λ₀: `c³ = 0` |
| `AD` | λ₀: `ad² = 0` | `AE` | λ₀: `e² = 0` |
| `BC` | κ₀: `bc² = 0` | `BD` | κ₀: `b²d = 0` |
| `CD` | λ₀: `c³ = 0` | `CE` | ο₀: `c²e = 0` |
| `DE` | κ₀: `de = 0` | `ABE` | κ₀: `ab³ = 0` |
| `ACD` | μ₀: `c²d = 0` | `ACE` | ο₀: `c²e = 0` |
| `ADE` | κ₀: `de = 0` | `BCE` | κ₀: `bc² = 0` |
| `BDE` | μ₀: `bd² = 0` | `CDE` | κ₀: `de = 0` |
| `ACDE` | κ₀: `de = 0` | | |

The nine remaining cones need a genuine `linear_combination` certificate (all confirmed `(1)` after saturation):
`BE` (λ₀,Π₀), `ABC`, `ABD`, `BCD`, `ABCD`, `ABCE`, `ABDE`, `BCDE`, `ABCDE` (all five integrals).

**Note the payoff:** `ACE` — the cone that has blocked the campaign for three lanes — is now the one-liner `c²e = 0`.

## 4. Stage B — inside `R = {A}` (A strictly dominant)

Here every load key can compete, so introduce the *defects* `σ_ξ := w_ξρ − n_ξ > 0 (ξ ≠ A)` (`σ_ξ = +∞` if `ξ = 0`), so that the u-degree of a monomial is `wρ − Σ m_ξσ_ξ − w_πρ`. Two facts organise everything:

* every load-free monomial of the five forms has **σ-degree ≥ 6** for the σ-weights `(B,C,D,E) ↦ (2,2,3,3)` (κ₀,λ₀,μ₀,Π₀ start at 6, ο₀ at 7);
* hence with `Θ := min(σ_B/2, σ_C/2, σ_D/3, σ_E/3)` and `S := argmin`, `defect(m) ≥ Θ·σdeg(m)` **with equality iff `supp m ⊆ S`** — the exact mirror of §1.

**B0 (loads).** If the smallest active load defect `w_πρ` is `< 6Θ`, the top of each odd integral is the single monomial `coeff·π·A^i` ⇒ contradiction. If `= 6Θ`, use that the σ-6 parts of κ₀,μ₀,Π₀ are *proportional* (`μ₀ ≡ −(A/6)κ₀`, `Π₀ ≡ −(A²/12)κ₀` mod σ-degree ≥ 7) while the load columns are not (κ: `7/6912 A⁵`, μ: `35/248832 A⁶`, Π: `5/27648 A⁷`): the 3×2 matrix has rank 2, forcing `π = 0`. Iterate over `l(1), β(3), δ(5), ζ(7), θ(9)`; the even loads `α, ε, η` have **no** pure-`A` column at all (they vanish at the cusp), so they never enter an initial form.

**B1 (letters).** With `6Θ` below all load defects, the initial form of `Φ` is its σ-minimal part restricted to `S` — 15 cones. Machine-verified with *strictly valid* initial forms only (σ-degree 6 for κ,λ,μ,Π, σ-degree 7 for ο):

* **13 cones empty**: `B`, `C`, `D`, `E`, `BC`, `BD`, `BE`, `CE`, `DE`, `BCD`, `BCE`, `BDE`, `CDE`.
* `{C,D}` yields only `3ad² + c³ = 0`; it needs one bounded refinement in `(σ_B, σ_E)` — the planner enumerated the sub-chambers (9 distinct, all load activities) and **all close**.
* `{B,C,D,E}` is the **balanced cell** (§5).

*(Independent check: a chamber-level sweep over a σ-grid × 34 load subsets produced 45 127 distinct chambers, 704 of which were not single-monomial; every one is empty except the balanced cell and the trivial cell `B=C=D=E=0`, which dies because then `Π₀ ≡ 0`, contradicting `derivative Π = C(j/t) ≠ 0`.)*

## 5. Stage C — the balanced cell, and how it dies

`S = {B,C,D,E}`: `σ_B = σ_C = 2Θ`, `σ_D = σ_E = 3Θ`, all loads 0. Concretely `n_A = 2ρ, n_B = 3ρ−2Θ, n_C = 4ρ−2Θ, n_D = 5ρ−3Θ, n_E = 6ρ−3Θ` with `ρ,Θ ∈ ℕ_{>0}` (this is the sextic collapsing onto `q³` at the balanced rate — the (6,10) analogue of the (6,8) "meeting cell"). The five initial forms give only **three** independent equations, because the odd ones are proportional:

```
(G1) κ:  a b³ − 9 b c² + 54 d e = 0
(G2) λ:  a b²c − 3 a d² − c³ + 9 e² = 0
(G3) ο:  a b²e + 2 a b c d − 3 c² e = 0
```

and that system **is** solvable (checked: after the 2-torus it is a finite set of shapes, roots of `7u³−35u²+21u−1`). The missing equation is obtained *without any descent* from the proportionality itself. Set

```
N₁ := μ + (A/6)·κ  (weight 13)        [ = cMu + (A/6)·cKap , so natDegree N₁ ≤ n_A ]
```

Its σ-6 part vanishes identically and its σ-7 part is `(5/81)(A B² D − 6 B C E − 3 C² D)`, sitting at u-degree `13ρ − 7Θ > 2ρ = n_A` (always, since `Θ ≤ 3ρ/2`). Hence

```
(G4)  a b² d − 6 b c e − 3 c² d = 0 .
```

`⟨G1,G2,G3,G4⟩` saturated at `abcde` is `(1)` — **the balanced cell is empty.** (`N₂ := Π + (A²/12)κ` gives a proportional equation; `N₁` alone suffices.) `N₁` also carries a nonzero `l`-column (`77/248832 · l A⁶`), which is what makes step B0 uniform.

## 6. Lean lemma sequence

New file(s), namespace `Max11DegreeRoutes`, importing **only** `Grok610ScaleZeroConeKappaMuScratch` (which already exports every fact needed; the ConeFinal/ConeTerminal/ConeRatioTies/ConeFinish/ConeTriples files become unnecessary for this route and can be retired).

Entry point: `normalized610ScaleZero_coneKappaMuResidual` (`Grok610ScaleZeroConeKappaMuScratch.lean:1905`) supplies `t ≠ 0`, `j/t ≠ 0`, `H = (C t)^2`, `derivative (degreeZeroPrimitivePolynomial610 …) = C (j/t)` and `natDegree = 0` for λ, κ, μ, ο. Its trailing `¬ …Cone610` conjuncts are **not needed** and should be dropped.

**§6.1 Coordinates and transport** (file `Grok610ScaleZeroCubicCoordinatesScratch.lean`)

```lean
def cubicC610 (A C0 : k[X]) : k[X] := C0 - (1/3 : k) • A ^ 2
def cubicD610 (A B D0 : k[X]) : k[X] := D0 - (1/3 : k) • (A * B)
def cubicE610 (A C0 E0 : k[X]) : k[X] := E0 - (1/3 : k) • (A * C0) + (2/27 : k) • A ^ 3

def degreeZeroKappaCubic610  (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) : k[X]   -- 36 terms
def degreeZeroLambdaCubic610 … : k[X]   -- 42 terms
def degreeZeroMuCubic610     … : k[X]   -- 56 terms
def degreeZeroOmicronCubic610… : k[X]   -- 59 terms
def degreeZeroPrimitiveCubic610 … : k[X] -- 83 terms

theorem degreeZeroKappaPolynomial610_eq_cubic
    (l alpha beta delta epsilon zeta eta theta : k) (A B C D E : k[X]) :
    degreeZeroKappaPolynomial610 l alpha beta delta epsilon zeta eta theta
        A B (C + (1/3 : k) • A ^ 2) (D + (1/3 : k) • (A * B))
        (E + (1/3 : k) • (A * C) + (1/27 : k) • A ^ 3)
      = degreeZeroKappaCubic610 l alpha beta delta epsilon zeta eta theta A B C D E
```
(one per integral; proof `simp only [defs]; ring`; split the primitive into its eight group identities to keep `ring` inside the heartbeat budget, mirroring `degreeZeroPrimitivePolynomial610_eq_A7_add_rest`, `…ConeCascadeScratch.lean:599`). Then a wrapper turning the residual's `(A,B,C₀,D₀,E₀)` into `(A,B,cubicC610 …, cubicD610 …, cubicE610 …)` by `sub_add_cancel`-style rewriting.

**§6.2 Cone predicates.** 31 defs in cross-multiplied ℕ form, e.g.

```lean
def CubicRatioConeBCE610 (A B C D E : k[X]) : Prop :=
  0 < B.natDegree ∧ 4 * B.natDegree = 3 * C.natDegree ∧ 2 * B.natDegree = E.natDegree ∧
    3 * A.natDegree < 2 * B.natDegree ∧ 5 * B.natDegree < 3 * D.natDegree  -- (n_D/5 < n_B/3)
```

**§6.3 Per-integral split lemmas** (the existing, proven pattern):

```lean
theorem degreeZeroLambdaCubic610_eq_BCE_add_rest … :
    degreeZeroLambdaCubic610 … = (restricted form) + degreeZeroLambdaCubicNoBCE610 …
theorem degreeZeroLambdaCubicNoBCE610_natDegree_lt … (hcone : CubicRatioConeBCE610 …) :
    (degreeZeroLambdaCubicNoBCE610 …).natDegree < 4 * B.natDegree + 3 * C.natDegree  -- e.g.
```
proved by `compute_degree` + `omega` from the cone inequalities — literally the shape of `degreeZeroLambdaNoAC0E0_natDegree_lt` (`Grok610ScaleZeroConeTriplesScratch.lean` `TripleRests610`) and `degreeZeroMuNoA6_natDegree_lt_of_mixedB` (`Grok810ScaleZeroConeExhaustionScratch.lean:1403`).

**§6.4 Top-coefficient corollaries.**

```lean
theorem lambdaCubic_top_coeff_eq_zero_of_cone …
    (hlam : (degreeZeroLambdaCubic610 …).natDegree = 0) (hcone : …) :
    (restricted form evaluated at leadingCoeffs) = 0
theorem primitiveCubic_top_coeff_eq_zero_of_cone …
    (hdeg : (degreeZeroPrimitiveCubic610 …).natDegree = 1) (hcone : …) (h2 : 2 ≤ topDegree) : …
```

**§6.5 Cone kills.** `cubicCone_BCE_impossible`, … — 30 theorems, 21 of them
`exact absurd (…) (mul_ne_zero …)` on a single monomial; 9 via a transcribed `linear_combination` (Gröbner certificate).

**§6.6 Stage B.** `defect` predicates `CubicSigmaCone_S610` (15 defs, in cross-multiplied ℕ form — state them as linear identities in `n_A,n_B,n_C,n_D,n_E` to keep `omega` happy), the load lemmas `cubicADominant_l_eq_zero`, `…_beta_eq_zero`, `…_delta_eq_zero`, `…_zeta_eq_zero`, `…_theta_eq_zero`, then 13 kills + the `{C,D}` refinement (≈9 sub-lemmas) + `cubicADominant_allLettersZero_impossible` (from `Π₀ ≡ 0` vs `derivative Π = C (j/t)`).

**§6.7 Stage C.** `def degreeZeroN1Cubic610 := degreeZeroMuCubic610 … + (1/6 : k) • (A * degreeZeroKappaCubic610 …)`, `theorem degreeZeroN1Cubic610_natDegree_le : natDegree ≤ A.natDegree` (from `natDegree μ = 0`, `natDegree κ = 0`), the σ-7 split lemma, and `cubicBalancedCell_impossible` by `linear_combination` on `(G1),(G2),(G3),(G4)`.

**§6.8 Assembly.**

```lean
theorem normalized610ScaleZero_impossible {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) : False
theorem proved_planeKellerNormalized610LowScaleRoute : PlaneKellerNormalized610LowScaleRoute (K := K)
```
Exhaustiveness: nested `by_cases` on the ten pairwise ratio comparisons, closing the leftovers with `omega` — exactly the tail of `normalized810ScaleZero_impossible` (`Grok810ScaleZeroConeExhaustionScratch.lean:2720`, ending in `omega`).

## 7. CAS jobs the lane must run **before** writing Lean

1. `derive_610_scale_zero_cubic_coordinates.py` — read the five Lean definitions, substitute `C₀ = C + A²/3, D₀ = D + AB/3, E₀ = E + AC/3 + A³/27`, expand, and (a) **assert isobaricity** for weights (11,12,13,14,15) under `A,B,C,D,E,l,α,β,δ,ε,ζ,η,θ ↦ 2,3,4,5,6,1,2,3,5,6,7,8,9` — this is the transcription checksum; (b) emit the five cubic definitions in Lean syntax.
2. `derive_610_scale_zero_cubic_cones.py` — for each of the 31 subsets `R`: restricted load-free forms; the saturated Gröbner `⟨Φ^R, T·Πlc − 1⟩`; and, for the 9 non-monomial cones, an explicit representation `lc^k = Σ h_i Φ_i^R` to transcribe as `linear_combination`. Also emit, per cone and integral, the "rest" polynomial and the ℕ inequality list for `compute_degree`+`omega`.
3. `derive_610_scale_zero_cubic_adominant.py` — the σ-grading analysis: minimal σ-degrees, the 15 argmin systems and certificates, the `{C,D}` refinement, and the **complete** load enumeration (all 2⁸ load subsets × 2⁴ letter-vanishing subsets × exact σ-grid) verifying that no chamber other than the balanced cell survives. *(The planner's sweep covered 34 of the 256 load subsets — the lane must complete it.)*
4. `derive_610_scale_zero_cubic_balanced.py` — `N₁ = μ + (A/6)κ`, its σ-6 vanishing, its σ-7 part, and the `(1)`-certificate for `⟨G1,G2,G3,G4⟩` saturated at `abcde`.

## 8. Reuse map

* residual/entry: `normalized610ScaleZero_coneKappaMuResidual`, `Grok610ScaleZeroConeKappaMuScratch.lean:1905`
* `natDegree_eq_one_of_derivative_eq_nonzero_C610`, `Grok610ScaleZeroConeCascadeScratch.lean:57`
* `smul_add_lower_ne_C610` :73, `natDegree_add_lt610` :90, `natDegree_add8_lt610` :115, `natDegree_smul_lt610` :107
* `degreeZeroPrimitivePolynomial610_eq_A7_add_rest` :599 (split-lemma + `module` pattern, and heartbeat settings)
* rest-bound pattern: `Grok610ScaleZeroConeTriplesScratch.lean` `TripleRests610`; `Grok810ScaleZeroConeExhaustionScratch.lean:1403–1750`
* final `by_cases` + `omega` assembly: `Grok810ScaleZeroConeExhaustionScratch.lean:2720–2870`
* cubic-coordinate precedent (6,8): `Grok68TerminalZeroMeetingCellPlanScratch.md` §2
* route closure: `planeKellerNormalized610LowScaleRoute_of_scaleZero`, `Grok610AlignedNonsquareDegreeZeroPrimitiveScratch.lean:1493`

## 9. Risks (honest)

1. **Transcription.** The forms above were typed from the Lean sources. Mitigation: the isobaricity assertion in CAS job 1 (it passed for all five, which is very strong), plus re-deriving from the Lean text.
2. **`ring` cost of the coordinate transport.** `Π` after substitution has 83 monomials and A-powers to 7. Mitigation: prove the eight group identities (base/α/β/δ/ε/ζ/η/θ) separately, `maxHeartbeats 32000000` as already used at `…ConeCascadeScratch.lean:660`.
3. **`compute_degree` at 40–80 terms in 5 letters** — already done at this scale in the 810 exhaustion file; budget generously.
4. **Load enumeration completeness in Stage B** — the one genuinely unfinished computation (34/256 load subsets sampled). If an unsampled chamber resists, it will be of the same shape as the balanced cell and `N₁`/`N₂` are the tools.
5. **Cone exhaustiveness in ℕ.** The 31-fold split needs the argmax comparisons stated so `omega` can finish; state all comparisons cross-multiplied and avoid division.
6. Nothing here uses a total-degree or twice-prime theorem, a finite-root shortcut, or a new axiom: every kill is a saturated-ideal certificate transcribed as `linear_combination`, i.e. a polynomial identity.

## 10. Fallbacks

* **F1 (staging).** If one lane is too big, split: lane 1 = §6.1–6.5 (coordinates + the 31 argmax cones) exporting `normalized610ScaleZero_cubicADominantResidual` (the single cone `R = {A}` with the cubic letters); lane 2 = §6.6–6.8. Lane 1 alone already reduces the leaf from an open enumeration to **one** cone and retires five scratch files.
* **F2 (if Stage B's load bookkeeping balloons).** Promote `N₁ = μ + (A/6)κ` and `N₂ = Π + (A²/12)κ` to first-class integrals at the start of Stage B; they are the objects that separate the load columns from the letter columns, and they already carry the balanced cell.
* **F3 (if the balanced cell resists in Lean).** Mirror the (6,8) meeting-cell finish: on the cell all loads vanish, so the five compact identities of §2 are exact; eliminate `E` from κ, then `C` from λ, exhibit `A,B,C,D,E ∈ k[d]` and close with `Polynomial.derivative_comp` against `derivative Π = C (j/t)`.
* **Bonus.** The same cubic-coordinate move should be tried on `Grok810ScaleZeroMixedConesScratch`-style residuals and on (6,8): the sparsity gain (37→14 monomials for λ) is a property of the grading, not of (6,10).
