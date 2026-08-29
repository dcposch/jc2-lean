import LowScale610ScaleZeroSource
import LowScale610ScaleTwoThirdFace

/-! # Scale-zero second cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroSourceScratch` on the constant core
`H = (C t)²`.  The first packet already forces the discriminator `N` and the
cleared first sextic/decic defect to ground constants.  This file consumes
the next unused Keller coefficient, the degree-`12` Jacobian row

```
10 B' + 9 L A' - 6 Q' = 0
```

of the same monic depression.  The corresponding first integral clears to
the weight-fifteen polynomial defect `T`, and at scale zero that defect is
again a ground-field constant.

No total-degree or twice-prime theorem is used.  A constant scale has no
finite root, so the scale-two third-face jet is unavailable.  Both the
vanishing and the nonzero constant branches of `λ` and of `T` are kept.
The packet does not close the leaf: unused Jacobian coefficients start at
degree `11`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ScaleZeroSecondDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/

/-- Source-facing degree-`12` Jacobian row of a normalized scale-zero
`(6,10)` pair. -/
theorem normalized610ScaleZero_thirdCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 6).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 5).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 4).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 3).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 7).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 8).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 9).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 10).derivative) =
      0 := by
  dsimp only
  rcases hsource with
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp6, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using thirdCoefficientJacobianRow_610 hp hq hjac

/-- At scale zero the common core is constant, so the leading sextic and
decic coefficients of the degree-`12` row are differential constants. -/
theorem scaleZero_thirdCoefficientJacobianRow_610
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 5).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 4).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 3).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 7).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 8).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 9).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp6der : (p.coeff 6).derivative = 0 := by
    rw [hp6, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := thirdCoefficientJacobianRow_610 hp hq hjac
  simpa [hp6der, hq10der] using hrow

/-- Source-facing scale-zero collapse of the degree-`12` row. -/
theorem normalized610ScaleZero_thirdCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 5).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 4).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 3).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 7).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 8).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 9).derivative) =
      0 := by
  dsimp only
  rcases hsource with
    ⟨_hH, hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using
    scaleZero_thirdCoefficientJacobianRow_610 hp hq hjac hHdegree
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)

/-! ## Weight-fifteen cleared defect after a square root of the core -/

/-- Strongest exact second residual after the constant-scale source bridge:
the cleared weight-fifteen sextic/decic defect is a scalar times `h¹⁵`.
Both the vanishing and the nonzero values of `λ` are permitted. -/
theorem scaleZero_secondClearedDefect_exists_C_610
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda alpha gamma : k),
      (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedSecondDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (q.coeff 8) lambda =
        Polynomial.C alpha * (Polynomial.C t) ^ 10 ∧
      localClearedThirdDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda =
        Polynomial.C gamma * (Polynomial.C t) ^ 15 := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  obtain ⟨lambda, hN⟩ :=
    scaleZero_discriminator_eq_C_mul_ninthPower_610 hp hq hjac ht hH hp6 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨alpha, halpha⟩ :=
    nonzeroFace610_secondDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  obtain ⟨gamma, hgamma⟩ :=
    nonzeroFace610_thirdDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  exact ⟨lambda, alpha, gamma, hN, halpha, hgamma⟩

/-- Aligned specialization of the weight-fifteen defect: the two
`λ`-monomials drop. -/
theorem localClearedThirdDefect610_of_lambda_zero
    (h a5 a4 a3 b8 b7 : k[X]) :
    localClearedThirdDefect610 h a5 a4 a3 b8 b7 0 =
      (520 : k[X]) * a5 ^ 3 -
        (864 : k[X]) * a5 * b8 * h ^ 2 +
        (720 : k[X]) * a4 * a5 * h ^ 6 +
        (648 : k[X]) * b7 * h ^ 8 -
        (1080 : k[X]) * a3 * h ^ 12 := by
  simp [localClearedThirdDefect610, map_zero]

variable [IsAlgClosed k]

/-- Source-facing second residual packet for a normalized scale-zero
`(6,10)` pair.  The constants `λ`, `α`, and `γ` may vanish. -/
theorem normalized610ScaleZero_exists_secondClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda alpha gamma : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedSecondDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          lambda =
        Polynomial.C alpha * (Polynomial.C t) ^ 10 ∧
      localClearedThirdDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          lambda =
        Polynomial.C gamma * (Polynomial.C t) ^ 15 := by
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
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨lambda, alpha, gamma, hN, halpha, hgamma⟩ :=
    scaleZero_secondClearedDefect_exists_C_610 hp hq hD ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  exact ⟨t, lambda, alpha, gamma, ht, hHsq,
    by simpa only [p, q] using hN,
    by simpa only [p, q] using halpha,
    by simpa only [p, q] using hgamma⟩

/-- At scale zero the weight-fifteen defect is a literal ground-field
constant. -/
theorem normalized610ScaleZero_secondClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda gamma : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedThirdDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          lambda =
        Polynomial.C gamma := by
  obtain ⟨t, lambda, _alpha, gamma, ht, hHsq, _hN, _hM, hT⟩ :=
    normalized610ScaleZero_exists_secondClearedDefect hsource
  refine ⟨t, lambda, gamma * t ^ 15, ht, hHsq, ?_⟩
  have hconst :
      localClearedThirdDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          lambda =
        Polynomial.C (gamma * t ^ 15) := by
    rw [hT, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) gamma (t ^ 15)).symm
  exact hconst

/-- Newton degree of the second cleared sextic/decic defect at scale zero. -/
theorem normalized610ScaleZero_secondClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedThirdDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, gamma, ht, hHsq, hT⟩ :=
    normalized610ScaleZero_secondClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hT]
  exact (natDegree_C gamma).le

/-- Exact second residual selector: `648 q₇ h⁸` differs from a polynomial
in the remaining third-defect monomials by a ground constant. -/
theorem normalized610ScaleZero_secondSourceResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda gamma : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (648 : k[X]) * q.coeff 7 * h0 ^ 8 =
        Polynomial.C gamma -
          ((520 : k[X]) * p.coeff 5 ^ 3 -
            (864 : k[X]) * p.coeff 5 * q.coeff 8 * h0 ^ 2 -
            (351 : k[X]) * Polynomial.C lambda * p.coeff 5 ^ 2 * h0 ^ 5 +
            (720 : k[X]) * p.coeff 4 * p.coeff 5 * h0 ^ 6 +
            (324 : k[X]) * Polynomial.C lambda * p.coeff 4 * h0 ^ 11 -
            (1080 : k[X]) * p.coeff 3 * h0 ^ 12) := by
  dsimp only
  obtain ⟨t, lambda, gamma, ht, hHsq, hT⟩ :=
    normalized610ScaleZero_secondClearedDefect_exists_C hsource
  refine ⟨t, lambda, gamma, ht, hHsq, ?_⟩
  simp only [localClearedThirdDefect610] at hT
  linear_combination hT

/-- Aligned/nonzero split of the scale-zero second cleared defect: it
vanishes, or it is a nonzero ground-field constant. -/
theorem normalized610ScaleZero_secondClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let T :=
        localClearedThirdDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          lambda
      T = 0 ∨ ∃ gamma : k, gamma ≠ 0 ∧ T = Polynomial.C gamma := by
  dsimp only
  obtain ⟨t, lambda, gamma, ht, hHsq, hT⟩ :=
    normalized610ScaleZero_secondClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  by_cases hgamma : gamma = 0
  · left
    simpa only [hgamma, Polynomial.C_0] using hT
  · exact Or.inr ⟨gamma, hgamma, hT⟩

/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-fifteen defect. -/
theorem normalized610ScaleZero_secondClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda gamma : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9
      let T :=
        localClearedThirdDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      T = Polynomial.C gamma ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (gamma = 0 ∧ T = 0 ∨
        gamma ≠ 0 ∧ T = Polynomial.C gamma) := by
  dsimp only
  obtain ⟨t, lambda, _alpha, gamma0, ht, hHsq, hN, _hM, hTpow⟩ :=
    normalized610ScaleZero_exists_secondClearedDefect hsource
  let gamma : k := gamma0 * t ^ 15
  have hT :
      localClearedThirdDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          lambda =
        Polynomial.C gamma := by
    rw [hTpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) gamma0 (t ^ 15)).symm
  refine ⟨t, lambda, gamma, ht, hHsq, hN, hT, ?_, ?_⟩
  · by_cases hlambda : lambda = 0
    · left
      refine ⟨hlambda, ?_⟩
      simpa only [hlambda, Polynomial.C_0, zero_mul] using hN
    · right
      refine ⟨hlambda, ?_⟩
      have hNconst :
          (5 : k[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
                  H ^ 2 -
              (3 : k[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
            Polynomial.C (lambda * t ^ 9) := by
        rw [hN, ← Polynomial.C_pow]
        exact (map_mul (Polynomial.C : k →+* k[X]) lambda (t ^ 9)).symm
      exact hNconst
  · by_cases hgamma : gamma = 0
    · left
      refine ⟨hgamma, ?_⟩
      simpa only [hgamma, Polynomial.C_0] using hT
    · exact Or.inr ⟨hgamma, hT⟩

/-- Aligned branch `N = 0`: the weight-fifteen defect is still a ground
constant, now with `λ = 0`. -/
theorem normalized610ScaleZero_secondClearedDefect_of_aligned
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (haligned :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t gamma : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedThirdDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          0 =
        Polynomial.C gamma := by
  obtain ⟨t, lambda, _alpha, gamma0, ht, hHsq, hN, _hM, hTpow⟩ :=
    normalized610ScaleZero_exists_secondClearedDefect hsource
  have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
    pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
  have hlambda : lambda = 0 := by
    have hmul : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
      hN.symm.trans haligned
    have hC : Polynomial.C lambda = 0 :=
      (mul_eq_zero.mp hmul).resolve_right ht9
    exact Polynomial.C_eq_zero.mp hC
  refine ⟨t, gamma0 * t ^ 15, ht, hHsq, ?_⟩
  have hT :
      localClearedThirdDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          0 =
        Polynomial.C (gamma0 * t ^ 15) := by
    rw [← hlambda, hTpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) gamma0 (t ^ 15)).symm
  exact hT

/-- Nonzero discriminator branch: `λ ≠ 0` and the weight-fifteen defect is
still a ground constant. -/
theorem normalized610ScaleZero_secondClearedDefect_of_nonzero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (hnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda gamma : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedThirdDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          lambda =
        Polynomial.C gamma := by
  obtain ⟨t, lambda, _alpha, gamma0, ht, hHsq, hN, _hM, hTpow⟩ :=
    normalized610ScaleZero_exists_secondClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro hzero
    apply hnonzero
    simpa only [hzero, Polynomial.C_0, zero_mul] using hN
  refine ⟨t, lambda, gamma0 * t ^ 15, ht, hlambda, hHsq, hN, ?_⟩
  have hT :
      localClearedThirdDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          lambda =
        Polynomial.C (gamma0 * t ^ 15) := by
    rw [hTpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) gamma0 (t ^ 15)).symm
  exact hT

end ScaleZeroSecondDefect610

#print axioms normalized610ScaleZero_thirdCoefficientJacobianRow
#print axioms scaleZero_thirdCoefficientJacobianRow_610
#print axioms normalized610ScaleZero_thirdCoefficientJacobianRow_collapsed
#print axioms scaleZero_secondClearedDefect_exists_C_610
#print axioms localClearedThirdDefect610_of_lambda_zero
#print axioms normalized610ScaleZero_exists_secondClearedDefect
#print axioms normalized610ScaleZero_secondClearedDefect_exists_C
#print axioms normalized610ScaleZero_secondClearedDefect_natDegree_le_zero
#print axioms normalized610ScaleZero_secondSourceResidual
#print axioms normalized610ScaleZero_secondClearedDefectFirstFace
#print axioms normalized610ScaleZero_secondClearedDefectBranches
#print axioms normalized610ScaleZero_secondClearedDefect_of_aligned
#print axioms normalized610ScaleZero_secondClearedDefect_of_nonzero

end Max11DegreeRoutes
