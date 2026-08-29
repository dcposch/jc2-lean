import LowScale610ScaleZeroSecondDefect
import LowScale610ScaleTwoFourthFace

/-! # Scale-zero third cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroSecondDefectScratch` on the constant core
`H = (C t)²`.  The second packet already forces the discriminator `N` and
the weight-fifteen defect `T` to ground constants.  This file consumes the
next unused Keller coefficient, the degree-`11` Jacobian row

```
(p₆)' (6 q₆) + (p₅)' (7 q₇) + (p₄)' (8 q₈) + (p₃)' (9 q₉) + (p₂)' (10 q₁₀)
  - (6 p₆) q₆' - (5 p₅) q₇' - (4 p₄) q₈' - (3 p₃) q₉' - (2 p₂) q₁₀' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is `10 C' + 9 L B' + 8 P A' - 4 A P' - 6 R' = 0`.  The
corresponding first integral clears to the weight-twenty polynomial
defect `U`, and at scale zero that defect is again a ground-field
constant.

No total-degree or twice-prime theorem is used.  A constant scale has no
finite root, so the scale-two fourth-face jet is unavailable.  Both the
vanishing and the nonzero constant branches of `λ` and of `U` are kept.
The packet does not close the leaf: unused Jacobian coefficients start at
degree `10`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ScaleZeroThirdDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/

/-- Source-facing degree-`11` Jacobian row of a normalized scale-zero
`(6,10)` pair. -/
theorem normalized610ScaleZero_fourthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 6).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 5).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 3).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 2).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 6).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 7).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 8).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 9).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 10).derivative) =
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
  simpa only [p, q] using fourthCoefficientJacobianRow_610 hp hq hjac

/-- At scale zero the common core is constant, so the leading sextic and
decic coefficients of the degree-`11` row are differential constants. -/
theorem scaleZero_fourthCoefficientJacobianRow_610
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 5).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 3).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 2).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 6).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 7).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 8).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 9).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp6der : (p.coeff 6).derivative = 0 := by
    rw [hp6, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := fourthCoefficientJacobianRow_610 hp hq hjac
  simpa [hp6der, hq10der] using hrow

/-- Source-facing scale-zero collapse of the degree-`11` row. -/
theorem normalized610ScaleZero_fourthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 5).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 3).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 2).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 6).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 7).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 8).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 9).derivative) =
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
    scaleZero_fourthCoefficientJacobianRow_610 hp hq hjac hHdegree
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)

/-! ## Weight-twenty cleared defect after a square root of the core -/

/-- Strongest exact third residual after the constant-scale source bridge:
the cleared weight-twenty sextic/decic defect is a scalar times `h²⁰`.
Both the vanishing and the nonzero values of `λ` are permitted. -/
theorem scaleZero_thirdClearedDefect_exists_C_610
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda alpha gamma delta : k),
      (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedSecondDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (q.coeff 8) lambda =
        Polynomial.C alpha * (Polynomial.C t) ^ 10 ∧
      localClearedThirdDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (q.coeff 8) (q.coeff 7) lambda =
        Polynomial.C gamma * (Polynomial.C t) ^ 15 ∧
      localClearedFourthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          lambda =
        Polynomial.C delta * (Polynomial.C t) ^ 20 := by
  obtain ⟨lambda, alpha, gamma, hN, halpha, hgamma⟩ :=
    scaleZero_secondClearedDefect_exists_C_610 hp hq hD ht hH hp6 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨delta, hdelta⟩ :=
    nonzeroFace610_fourthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  exact ⟨lambda, alpha, gamma, delta, hN, halpha, hgamma, hdelta⟩

/-- Aligned specialization of the weight-twenty defect: the three
`λ`-monomials drop. -/
theorem localClearedFourthDefect610_of_lambda_zero
    (h a5 a4 a3 a2 b8 b7 b6 : k[X]) :
    localClearedFourthDefect610 h a5 a4 a3 a2 b8 b7 b6 0 =
      -(360 : k[X]) * a5 ^ 4 +
        (576 : k[X]) * a5 ^ 2 * b8 * h ^ 2 -
        (576 : k[X]) * a4 * b8 * h ^ 8 -
        (504 : k[X]) * a5 * b7 * h ^ 8 +
        (720 : k[X]) * a4 ^ 2 * h ^ 12 +
        (360 : k[X]) * a5 * a3 * h ^ 12 +
        (432 : k[X]) * b6 * h ^ 14 -
        (720 : k[X]) * a2 * h ^ 18 := by
  simp [localClearedFourthDefect610, map_zero]

variable [IsAlgClosed k]

/-- Source-facing third residual packet for a normalized scale-zero
`(6,10)` pair.  The constants `λ`, `α`, `γ`, and `δ` may vanish. -/
theorem normalized610ScaleZero_exists_thirdClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda alpha gamma delta : k),
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
        Polynomial.C gamma * (Polynomial.C t) ^ 15 ∧
      localClearedFourthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          lambda =
        Polynomial.C delta * (Polynomial.C t) ^ 20 := by
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
  obtain ⟨lambda, alpha, gamma, delta, hN, halpha, hgamma, hdelta⟩ :=
    scaleZero_thirdClearedDefect_exists_C_610 hp hq hD ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  exact ⟨t, lambda, alpha, gamma, delta, ht, hHsq,
    by simpa only [p, q] using hN,
    by simpa only [p, q] using halpha,
    by simpa only [p, q] using hgamma,
    by simpa only [p, q] using hdelta⟩

/-- At scale zero the weight-twenty defect is a literal ground-field
constant. -/
theorem normalized610ScaleZero_thirdClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda delta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedFourthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          lambda =
        Polynomial.C delta := by
  obtain ⟨t, lambda, _alpha, _gamma, delta, ht, hHsq, _hN, _hM, _hT, hU⟩ :=
    normalized610ScaleZero_exists_thirdClearedDefect hsource
  refine ⟨t, lambda, delta * t ^ 20, ht, hHsq, ?_⟩
  have hconst :
      localClearedFourthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          lambda =
        Polynomial.C (delta * t ^ 20) := by
    rw [hU, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) delta (t ^ 20)).symm
  exact hconst

/-- Newton degree of the third cleared sextic/decic defect at scale zero. -/
theorem normalized610ScaleZero_thirdClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedFourthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, delta, ht, hHsq, hU⟩ :=
    normalized610ScaleZero_thirdClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hU]
  exact (natDegree_C delta).le

/-- Exact third residual selector: `432 q₆ h¹⁴` differs from a polynomial
in the remaining fourth-defect monomials by a ground constant. -/
theorem normalized610ScaleZero_thirdSourceResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda delta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (432 : k[X]) * q.coeff 6 * h0 ^ 14 =
        Polynomial.C delta -
          (-(360 : k[X]) * p.coeff 5 ^ 4 +
            (576 : k[X]) * p.coeff 5 ^ 2 * q.coeff 8 * h0 ^ 2 +
            (216 : k[X]) * Polynomial.C lambda * p.coeff 5 ^ 3 * h0 ^ 5 -
            (576 : k[X]) * p.coeff 4 * q.coeff 8 * h0 ^ 8 -
            (504 : k[X]) * p.coeff 5 * q.coeff 7 * h0 ^ 8 -
            (432 : k[X]) * Polynomial.C lambda * p.coeff 5 * p.coeff 4 *
              h0 ^ 11 +
            (720 : k[X]) * p.coeff 4 ^ 2 * h0 ^ 12 +
            (360 : k[X]) * p.coeff 5 * p.coeff 3 * h0 ^ 12 +
            (216 : k[X]) * Polynomial.C lambda * p.coeff 3 * h0 ^ 17 -
            (720 : k[X]) * p.coeff 2 * h0 ^ 18) := by
  dsimp only
  obtain ⟨t, lambda, delta, ht, hHsq, hU⟩ :=
    normalized610ScaleZero_thirdClearedDefect_exists_C hsource
  refine ⟨t, lambda, delta, ht, hHsq, ?_⟩
  simp only [localClearedFourthDefect610] at hU
  linear_combination hU

/-- Aligned/nonzero split of the scale-zero third cleared defect: it
vanishes, or it is a nonzero ground-field constant. -/
theorem normalized610ScaleZero_thirdClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let U :=
        localClearedFourthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          lambda
      U = 0 ∨ ∃ delta : k, delta ≠ 0 ∧ U = Polynomial.C delta := by
  dsimp only
  obtain ⟨t, lambda, delta, ht, hHsq, hU⟩ :=
    normalized610ScaleZero_thirdClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  by_cases hdelta : delta = 0
  · left
    simpa only [hdelta, Polynomial.C_0] using hU
  · exact Or.inr ⟨delta, hdelta, hU⟩

/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-twenty defect. -/
theorem normalized610ScaleZero_thirdClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda delta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9
      let U :=
        localClearedFourthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      U = Polynomial.C delta ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (delta = 0 ∧ U = 0 ∨
        delta ≠ 0 ∧ U = Polynomial.C delta) := by
  dsimp only
  obtain ⟨t, lambda, _alpha, _gamma, delta0, ht, hHsq, hN, _hM, _hT, hUpow⟩ :=
    normalized610ScaleZero_exists_thirdClearedDefect hsource
  let delta : k := delta0 * t ^ 20
  have hU :
      localClearedFourthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          lambda =
        Polynomial.C delta := by
    rw [hUpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) delta0 (t ^ 20)).symm
  refine ⟨t, lambda, delta, ht, hHsq, hN, hU, ?_, ?_⟩
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
  · by_cases hdelta : delta = 0
    · left
      refine ⟨hdelta, ?_⟩
      simpa only [hdelta, Polynomial.C_0] using hU
    · exact Or.inr ⟨hdelta, hU⟩

/-- Aligned branch `N = 0`: the weight-twenty defect is still a ground
constant, now with `λ = 0`. -/
theorem normalized610ScaleZero_thirdClearedDefect_of_aligned
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (haligned :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t delta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedFourthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          0 =
        Polynomial.C delta := by
  obtain ⟨t, lambda, _alpha, _gamma, delta0, ht, hHsq, hN, _hM, _hT, hUpow⟩ :=
    normalized610ScaleZero_exists_thirdClearedDefect hsource
  have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
    pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
  have hlambda : lambda = 0 := by
    have hmul : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
      hN.symm.trans haligned
    have hC : Polynomial.C lambda = 0 :=
      (mul_eq_zero.mp hmul).resolve_right ht9
    exact Polynomial.C_eq_zero.mp hC
  refine ⟨t, delta0 * t ^ 20, ht, hHsq, ?_⟩
  have hU :
      localClearedFourthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          0 =
        Polynomial.C (delta0 * t ^ 20) := by
    rw [← hlambda, hUpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) delta0 (t ^ 20)).symm
  exact hU

/-- Nonzero discriminator branch: `λ ≠ 0` and the weight-twenty defect is
still a ground constant. -/
theorem normalized610ScaleZero_thirdClearedDefect_of_nonzero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (hnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda delta : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedFourthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          lambda =
        Polynomial.C delta := by
  obtain ⟨t, lambda, _alpha, _gamma, delta0, ht, hHsq, hN, _hM, _hT, hUpow⟩ :=
    normalized610ScaleZero_exists_thirdClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro hzero
    apply hnonzero
    simpa only [hzero, Polynomial.C_0, zero_mul] using hN
  refine ⟨t, lambda, delta0 * t ^ 20, ht, hlambda, hHsq, hN, ?_⟩
  have hU :
      localClearedFourthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          lambda =
        Polynomial.C (delta0 * t ^ 20) := by
    rw [hUpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) delta0 (t ^ 20)).symm
  exact hU

end ScaleZeroThirdDefect610

#print axioms normalized610ScaleZero_fourthCoefficientJacobianRow
#print axioms scaleZero_fourthCoefficientJacobianRow_610
#print axioms normalized610ScaleZero_fourthCoefficientJacobianRow_collapsed
#print axioms scaleZero_thirdClearedDefect_exists_C_610
#print axioms localClearedFourthDefect610_of_lambda_zero
#print axioms normalized610ScaleZero_exists_thirdClearedDefect
#print axioms normalized610ScaleZero_thirdClearedDefect_exists_C
#print axioms normalized610ScaleZero_thirdClearedDefect_natDegree_le_zero
#print axioms normalized610ScaleZero_thirdSourceResidual
#print axioms normalized610ScaleZero_thirdClearedDefectFirstFace
#print axioms normalized610ScaleZero_thirdClearedDefectBranches
#print axioms normalized610ScaleZero_thirdClearedDefect_of_aligned
#print axioms normalized610ScaleZero_thirdClearedDefect_of_nonzero

end Max11DegreeRoutes
