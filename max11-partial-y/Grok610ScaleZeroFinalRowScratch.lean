import Grok610ScaleZeroDegreeOneRowScratch
import Sol610ScaleTwoDegreeZeroDifferentialBridgeScratch

/-! # Scale-zero final Jacobian row for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroDegreeOneRowScratch` on the constant
core `H = (C t)²`.  The degree-one packet already forces the discriminator
`N` and every cleared defect through the weight-seventy fourth tail `ο`
to ground constants, including the exact selectors `172186884 p₀ q₄ h⁵⁶`
and `6291456 p₀ q₃ h⁶²`.  This file consumes the last unused Keller
coefficient, the inhomogeneous degree-`0` Jacobian row

```
(p₀)' q₁ - p₁ (q₀)' = j
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is `W E' - D X' = j / h`.  Unlike every higher row it equals
the nonzero Keller constant, so it is not a first integral and it
clears no further defect.  Its companion is the already-landed
weight-fifteen primitive: on a monic sextic/decic bracket the primitive
differentiates to the same constant `j / h`.  At this scale `h = C t`
is a nonzero scalar, so both identities are polynomial-degree
bookkeeping in `k[X]` — a nonzero constant Wronskian, and a primitive
whose derivative is the nonzero constant `j / t`.

A constant core has no finite root, so the scale-two square-chamber
`S0/S1` peel is unavailable: those identities do not drop Newton
degree when `h` is constant.  The endgame at this scale is the same
valuation exhaustion as the `(4,10)` constant-core assembly — the
accumulated weight-`h^k` ground constants from the defect tower,
together with the last row, overdetermine the remaining free core
`(A, B, C₀, D₀, E₀)` after triangular integration of the decic
coordinates.  That integration-and-degree cascade is not claimed here.

The Jacobian coefficient tower is fully consumed: there is no unused
row below degree `0`.  The packet does not close the leaf.  Both the
vanishing and the nonzero constant branches of `λ` and of the
weight-sixty-five and weight-seventy defects are kept.  One exact
chamber is excluded: if both `p₀` and `q₀` are constants then the last
row collapses to `0 = j`, contradicting `j ≠ 0`.  No total-degree or
twice-prime theorem is used.  No finite-root shortcut is used.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedSectionVars false

section ScaleZeroFinalRow610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal last Keller coefficient -/

/-- The degree-`0` Jacobian coefficient for outer degrees `(6,10)` is
the last row of the tower and is inhomogeneous: `W E' - D X' = j`, the
Keller constant itself.  There is no unused row below it. -/
theorem scaleZeroRaw_fifteenthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 0).derivative * q.coeff 1 -
      p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 0) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 0 :
      Finset (ℕ × ℕ)) =
      ({(0, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num at hcoeff
  linear_combination hcoeff

/-- Source-facing degree-`0` Jacobian row of a normalized scale-zero
`(6,10)` pair.  The Keller constant is nonzero. -/
theorem normalized610ScaleZero_fifteenthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ j : k, j ≠ 0 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  dsimp only
  rcases hsource with
    ⟨_hH, _hHdegree, _hPdegree, _hQdegree, _hp6, _hq10, hKeller⟩
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  refine ⟨j, hj, ?_⟩
  simpa using scaleZeroRaw_fifteenthCoefficientJacobianRow_610 hjac

/-- At scale zero the common core is constant; the degree-`0` row has no
`p₆'` or `q₁₀'` term, so it collapses to the same literal row. -/
theorem scaleZero_fifteenthCoefficientJacobianRow_610
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 0).derivative * q.coeff 1 -
      p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp6der : (p.coeff 6).derivative = 0 := by
    rw [hp6, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := scaleZeroRaw_fifteenthCoefficientJacobianRow_610 hjac
  simpa [hp6der, hq10der] using hrow

/-- Source-facing scale-zero collapse of the degree-`0` row. -/
theorem normalized610ScaleZero_fifteenthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ j : k, j ≠ 0 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j :=
  normalized610ScaleZero_fifteenthCoefficientJacobianRow hsource

/-- The last source row is a ground-field constant, and that constant is
the nonzero Keller parameter. -/
theorem normalized610ScaleZero_finalRow_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ j : k, j ≠ 0 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j :=
  normalized610ScaleZero_fifteenthCoefficientJacobianRow hsource

/-- Newton degree of the last Keller coefficient at scale zero: the
source Wronskian is a nonzero constant polynomial. -/
theorem normalized610ScaleZero_finalRow_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    ((p.coeff 0).derivative * q.coeff 1 -
      p.coeff 1 * (q.coeff 0).derivative).natDegree ≤ 0 := by
  dsimp only
  obtain ⟨j, _hj, hrow⟩ :=
    normalized610ScaleZero_finalRow_exists_C hsource
  rw [hrow]
  exact (natDegree_C j).le

/-- The two cross-products on the last row are unequal as polynomials:
`p₀' q₁ ≠ p₁ q₀'`.  This is the scale-zero form of the scale-two
boundary separation, now global rather than evaluated at a root. -/
theorem normalized610ScaleZero_finalRow_crossProducts_ne
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 0).derivative * q.coeff 1 ≠
      p.coeff 1 * (q.coeff 0).derivative := by
  dsimp only
  obtain ⟨j, hj, hrow⟩ :=
    normalized610ScaleZero_finalRow_exists_C hsource
  intro heq
  apply hj
  have : Polynomial.C j = (0 : k[X]) := by
    rw [← hrow, heq, sub_self]
  exact Polynomial.C_eq_zero.mp this

/-- Constant-lowest-coefficient chamber: if both `p₀` and `q₀` are
ground constants then the last row collapses to `0 = j`. -/
theorem normalized610ScaleZero_false_of_constant_p0_q0
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (hp0 :
      (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0).natDegree =
        0)
    (hq0 :
      (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0).natDegree =
        0) :
    False := by
  obtain ⟨j, hj, hrow⟩ :=
    normalized610ScaleZero_finalRow_exists_C hsource
  obtain ⟨c0, hc0⟩ := natDegree_eq_zero.mp hp0
  obtain ⟨d0, hd0⟩ := natDegree_eq_zero.mp hq0
  have hp0der :
      (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0).derivative =
        0 := by
    rw [← hc0, derivative_C]
  have hq0der :
      (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0).derivative =
        0 := by
    rw [← hd0, derivative_C]
  have : Polynomial.C j = (0 : k[X]) := by
    rw [← hrow, hp0der, hq0der, zero_mul, mul_zero, sub_zero]
  exact hj (Polynomial.C_eq_zero.mp this)

/-! ## Depressed last row and the weight-fifteen primitive -/

/-- After the constant-scale monic depression the last row is the
nonzero constant `j / t`.  No finite root is used. -/
theorem scaleZero_normalizedDegreeZeroRow_610
    {p q : k[X][X]} {j t : k}
    (ht : t ≠ 0)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    let hRF : RatFunc k := RatFunc.C t
    let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
    let f : (RatFunc k)[X] :=
      affineDepress68 hRF (sexticDepressionR610 hRF a5)
        (sourceToRatFunc68 p)
    let g : (RatFunc k)[X] :=
      affineDepress68 hRF (sexticDepressionR610 hRF a5)
        (sourceToRatFunc68 q)
    g.coeff 1 * ratFuncDerivation68 (f.coeff 0) -
      f.coeff 1 * ratFuncDerivation68 (g.coeff 0) =
        RatFunc.C (j / t) := by
  dsimp only
  let hRF : RatFunc k := RatFunc.C t
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  have hh : hRF ≠ 0 := by
    intro hzero
    apply ht
    apply RatFunc.C_injective
    simpa only [hRF, map_zero] using hzero
  have hbracket :=
    differentialJacobian_affineDepress_sourceToRatFunc68 p q j hRF
      (sexticDepressionR610 hRF a5) hh hD
  have hcoeff :=
    congrArg (fun r : (RatFunc k)[X] => r.coeff 0) hbracket
  have hrow :
      (affineDepress68 hRF (sexticDepressionR610 hRF a5)
            (sourceToRatFunc68 q)).coeff 1 *
          ratFuncDerivation68
            ((affineDepress68 hRF (sexticDepressionR610 hRF a5)
              (sourceToRatFunc68 p)).coeff 0) -
        (affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 p)).coeff 1 *
          ratFuncDerivation68
            ((affineDepress68 hRF (sexticDepressionR610 hRF a5)
              (sourceToRatFunc68 q)).coeff 0) =
        RatFunc.C j / hRF := by
    have hzero := (differentialJacobian_coeff_0 ratFuncDerivation68
      (affineDepress68 hRF (sexticDepressionR610 hRF a5)
        (sourceToRatFunc68 p))
      (affineDepress68 hRF (sexticDepressionR610 hRF a5)
        (sourceToRatFunc68 q))).symm.trans hcoeff
    simpa [Polynomial.coeff_C] using hzero
  have hdiv : RatFunc.C j / hRF = RatFunc.C (j / t) := by
    simp only [hRF, map_div₀]
  exact hrow.trans hdiv

set_option maxHeartbeats 16000000 in
/-- On the same supplied constant-scale source, the weight-fifteen
primitive differentiates to the nonzero constant `j / t`.  This is the
`(4,10)` ground-integration identity at the last row, not a first
integral. -/
theorem scaleZero_degreeZeroPrimitive_deriv_eq_C_610
    {p q : k[X][X]} {j t lambda : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 -
      (3 : k[X]) * q.coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    let hRF : RatFunc k := RatFunc.C t
    let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
    let f : (RatFunc k)[X] :=
      affineDepress68 hRF (sexticDepressionR610 hRF a5)
        (sourceToRatFunc68 p)
    let g : (RatFunc k)[X] :=
      affineDepress68 hRF (sexticDepressionR610 hRF a5)
        (sourceToRatFunc68 q)
    Differential.deriv
        (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
          (g.coeff 1) (g.coeff 0)) =
      RatFunc.C (j / t) := by
  dsimp only
  let hRF : RatFunc k := RatFunc.C t
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5)
      (sourceToRatFunc68 q)
  have hh : hRF ≠ 0 := by
    intro hzero
    apply ht
    apply RatFunc.C_injective
    simpa only [hRF, map_zero] using hzero
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = hRF ^ 6 := by
    simp only [hp6, hH, hRF, map_pow, RatFunc.algebraMap_C]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow, RatFunc.algebraMap_C]
    ring
  have hpDep := affineDepress_sourceSextic68 p hRF
    (sexticDepressionR610 hRF a5) hp hh hpTop rfl
  have hNrat :
      5 * a5 * hRF ^ 4 - 3 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH2 : algebraMap k[X] (RatFunc k) (H ^ 2) = hRF ^ 4 := by
      simp only [hH, hRF, map_pow, RatFunc.algebraMap_C]
      ring
    have hh9 : algebraMap k[X] (RatFunc k) ((Polynomial.C t) ^ 9) =
        hRF ^ 9 := by
      simp only [hRF, map_pow, RatFunc.algebraMap_C]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9) =
        5 * a5 * hRF ^ 4 - 3 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a5, b9, hH2]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * (Polynomial.C t) ^ 9) =
        RatFunc.C lambda * hRF ^ 9 := by
      simp only [map_mul, RatFunc.algebraMap_C, hh9]
    exact hleft.symm.trans (hmapped.trans hright)
  have hLval :
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 =
        RatFunc.C (-lambda / 3) := by
    have hL := depressedL610_eq_of_ninthPower hRF a5 b9
      (RatFunc.C lambda) hh (by simpa using hNrat)
    simpa [map_neg, map_div₀, map_ofNat] using hL
  have hbracket := differentialJacobian_affineDepress_sourceToRatFunc68
    p q j hRF (sexticDepressionR610 hRF a5) hh hD
  have hf5 : f.coeff 5 = 0 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_five]
  have hf6 : f.coeff 6 = 1 := by
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_six]
  have hf_high : ∀ n, 6 < n → f.coeff n = 0 := by
    intro n hn
    dsimp only [f]
    rw [hpDep, coeff_depressedSextic68_of_gt_six _ _ _ _ _ hn]
  have hg_high_src : ∀ n, 10 < n →
      (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, _hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg9L : g.coeff 9 =
      depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
    dsimp only [g]
    rw [hg9]
    simp [depressedL610, depressedL810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9]
  have hg9const : g.coeff 9 = RatFunc.C (-lambda / 3) := by
    rw [hg9L, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9const]
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 3) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hprim :
      Differential.deriv
          (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 1) (g.coeff 0)) =
        RatFunc.C j / hRF :=
    degreeZeroPrimitive610_ratFuncDeriv_eq_simplePole f g j hRF
      hf_high hf6 hf5 hg_high hg10 hLconst
      (by simpa only [f, g] using hbracket)
  have hdiv : RatFunc.C j / hRF = RatFunc.C (j / t) := by
    simp only [hRF, map_div₀]
  exact hprim.trans hdiv

variable [IsAlgClosed k]

/-- Source-facing last-row packet: the Keller constant is nonzero, the
source Wronskian equals that constant, and after the constant-scale
monic depression the weight-fifteen primitive differentiates to
`j / t`.  The degree-one residual `ο` is preserved. -/
theorem normalized610ScaleZero_exists_degreeZeroPrimitive
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron : k),
      t ≠ 0 ∧
      j ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      nonzeroLocalClearedFourteenthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (Polynomial.C lambda) =
        Polynomial.C omicron ∧
      let hRF : RatFunc k := RatFunc.C t
      let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 p)
      let g : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 q)
      Differential.deriv
          (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 1) (g.coeff 0)) =
        RatFunc.C (j / t) := by
  dsimp only
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  obtain ⟨t, ht, hHsq⟩ :=
    scaleZero_exists_constantSquareRoot_610 hH hHdegree
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  have hrow :
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j :=
    scaleZeroRaw_fifteenthCoefficientJacobianRow_610 hjac
  obtain ⟨lambda, _a, _g, _d, _e, _z, _et, _th, _iot, _ka, _mu, _nu, _xi,
      omicron0, hN, _hM, _hT, _hU, _hV, _hW, _hX, _hY, _hI, _hZ, _hJ, _hnu,
      _hxi, homicron⟩ :=
    scaleZero_degreeOneClearedDefect_exists_C_610 hp hq hD ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  have homicronC :
      nonzeroLocalClearedFourteenthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (Polynomial.C lambda) =
        Polynomial.C (omicron0 * t ^ 70) := by
    rw [homicron, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) omicron0 (t ^ 70)).symm
  have hprim :=
    scaleZero_degreeZeroPrimitive_deriv_eq_C_610 hp hq ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hN) hD
  refine ⟨t, j, lambda, omicron0 * t ^ 70, ht, hj, hHsq,
    by simpa only [p, q] using hrow,
    by simpa only [p, q] using homicronC, ?_⟩
  simpa only [p, q] using hprim

/-- The degree-one packet's exact residual selector
`6291456 p₀ q₃ h⁶²` remains available on the final-row packet. -/
theorem normalized610ScaleZero_twelfthSourceResidual_preserved_final
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda xi : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (6291456 : k[X]) * p.coeff 0 * q.coeff 3 * h0 ^ 62 =
        Polynomial.C xi -
          (localClearedThirteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
              (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
              lambda -
            (6291456 : k[X]) * p.coeff 0 * q.coeff 3 * h0 ^ 62) :=
  normalized610ScaleZero_twelfthSourceResidual_preserved hsource

/-- Polynomial representatives of every affine-depressed coefficient
remain available: a constant scale has no finite pole. -/
theorem normalized610ScaleZero_finalRow_polynomialRepresentatives
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ScaleZero610AffineDepressPolynomialPacket P Q H :=
  normalized610ScaleZero_affineDepress_polynomialRepresentatives hsource

/-- Exhausted constant-core packet: every Jacobian coefficient through
degree `0` is consumed, the defect tower remains a list of ground
constants, and the weight-fifteen primitive differentiates to the
nonzero constant `j / t`.  The leaf is not closed. -/
theorem normalized610ScaleZero_exhaustedPacket
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron : k),
      t ≠ 0 ∧
      j ≠ 0 ∧
      j / t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      nonzeroLocalClearedFourteenthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (Polynomial.C lambda) =
        Polynomial.C omicron := by
  obtain ⟨t, j, lambda, omicron, ht, hj, hHsq, hrow, homicron, _hprim⟩ :=
    normalized610ScaleZero_exists_degreeZeroPrimitive hsource
  exact ⟨t, j, lambda, omicron, ht, hj, div_ne_zero hj ht, hHsq, hrow,
    homicron⟩

/-- Honest residual of the fully consumed Jacobian tower.

The last row is the inhomogeneous identity `p₀' q₁ - p₁ q₀' = C j`
with `j ≠ 0`.  After the constant-scale monic depression that identity
is `E' W - D X' = j / t`, and the weight-fifteen primitive
differentiates to the same nonzero constant.  Every cleared defect of
the tower remains a ground constant.  There is no unused Jacobian
coefficient.

The leaf is not closed.  A constant core has no finite root, so the
scale-two square-chamber `S0/S1` peel does not drop Newton degree.  The
missing input for `normalized610ScaleZero`-style `False` is the
`(4,10)`-style polynomial-trajectory valuation exhaustion of the
remaining free core `(A, B, C₀, D₀, E₀)` against those constant defects
together with the inhomogeneous identity that the weight-fifteen
primitive has derivative `C (j / t) ≠ 0`. -/
theorem normalized610ScaleZero_finalRowResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t j lambda omicron : k),
      t ≠ 0 ∧
      j ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      nonzeroLocalClearedFourteenthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (Polynomial.C lambda) =
        Polynomial.C omicron ∧
      let hRF : RatFunc k := RatFunc.C t
      let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
      let f : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 p)
      let g : (RatFunc k)[X] :=
        affineDepress68 hRF (sexticDepressionR610 hRF a5)
          (sourceToRatFunc68 q)
      Differential.deriv
          (degreeZeroPrimitive610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3) (g.coeff 2)
            (g.coeff 1) (g.coeff 0)) =
        RatFunc.C (j / t) :=
  normalized610ScaleZero_exists_degreeZeroPrimitive hsource

/-- Aligned discriminator branch: `λ = 0` still has a nonzero last row. -/
theorem normalized610ScaleZero_finalRow_of_aligned
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (haligned :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t j omicron : k),
      t ≠ 0 ∧
      j ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      nonzeroLocalClearedFourteenthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          0 =
        Polynomial.C omicron := by
  obtain ⟨j, hj, hrow⟩ :=
    normalized610ScaleZero_finalRow_exists_C hsource
  obtain ⟨t, omicron, ht, hHsq, hO⟩ :=
    normalized610ScaleZero_degreeOneClearedDefect_of_aligned hsource
      haligned
  exact ⟨t, j, omicron, ht, hj, hHsq, hrow, hO⟩

/-- Nonzero discriminator branch: `λ ≠ 0` and the last row is still the
nonzero Keller constant. -/
theorem normalized610ScaleZero_finalRow_of_nonzero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (hnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t j lambda omicron : k),
      t ≠ 0 ∧
      j ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5) *
            H ^ 2 -
        (3 : k[X]) *
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9) =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      (p.coeff 0).derivative * q.coeff 1 -
        p.coeff 1 * (q.coeff 0).derivative = Polynomial.C j ∧
      nonzeroLocalClearedFourteenthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 0)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 1)
          (Polynomial.C lambda) =
        Polynomial.C omicron := by
  obtain ⟨j, hj, hrow⟩ :=
    normalized610ScaleZero_finalRow_exists_C hsource
  obtain ⟨t, lambda, omicron, ht, hlambda, hHsq, hN, hO⟩ :=
    normalized610ScaleZero_degreeOneClearedDefect_of_nonzero hsource
      hnonzero
  exact ⟨t, j, lambda, omicron, ht, hj, hlambda, hHsq, hN, hrow, hO⟩

end ScaleZeroFinalRow610

#print axioms scaleZeroRaw_fifteenthCoefficientJacobianRow_610
#print axioms scaleZero_fifteenthCoefficientJacobianRow_610
#print axioms normalized610ScaleZero_fifteenthCoefficientJacobianRow
#print axioms normalized610ScaleZero_fifteenthCoefficientJacobianRow_collapsed
#print axioms normalized610ScaleZero_finalRow_exists_C
#print axioms normalized610ScaleZero_finalRow_natDegree_le_zero
#print axioms normalized610ScaleZero_finalRow_crossProducts_ne
#print axioms normalized610ScaleZero_false_of_constant_p0_q0
#print axioms scaleZero_normalizedDegreeZeroRow_610
#print axioms scaleZero_degreeZeroPrimitive_deriv_eq_C_610
#print axioms normalized610ScaleZero_exists_degreeZeroPrimitive
#print axioms normalized610ScaleZero_twelfthSourceResidual_preserved_final
#print axioms normalized610ScaleZero_finalRow_polynomialRepresentatives
#print axioms normalized610ScaleZero_exhaustedPacket
#print axioms normalized610ScaleZero_finalRowResidual
#print axioms normalized610ScaleZero_finalRow_of_aligned
#print axioms normalized610ScaleZero_finalRow_of_nonzero

end Max11DegreeRoutes
