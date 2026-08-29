import LowScale610ScaleZeroThirdDefect
import LowScale610ScaleTwoFifthFace

/-! # Scale-zero fourth cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `LowScale610ScaleZeroThirdDefect` on the constant core
`H = (C t)²`.  The third packet already forces the discriminator `N` and
the weight-twenty defect `U` to ground constants.  This file consumes the
next unused Keller coefficient, the degree-`10` Jacobian row

```
(p₆)' (5 q₅) + (p₅)' (6 q₆) + (p₄)' (7 q₇) + (p₃)' (8 q₈) + (p₂)' (9 q₉)
  + (p₁)' (10 q₁₀)
  - (6 p₆) q₅' - (5 p₅) q₆' - (4 p₄) q₇' - (3 p₃) q₈' - (2 p₂) q₉'
  - (1 p₁) q₁₀' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is
`10 D' + 9 L C' + 8 P B' + 7 Q A' - 3 B P' - 4 A Q' - 6 S' = 0`.  The
corresponding first integral clears to the weight-twenty-five polynomial
defect `V`, and at scale zero that defect is again a ground-field
constant.

No total-degree or twice-prime theorem is used.  A constant scale has no
finite root, so the scale-two fifth-face jet is unavailable.  Both the
vanishing and the nonzero constant branches of `λ` and of `V` are kept.
The packet does not close the leaf: unused Jacobian coefficients start at
degree `9`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ScaleZeroFourthDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/

/-- Source-facing degree-`10` Jacobian row of a normalized scale-zero
`(6,10)` pair. -/
theorem normalized610ScaleZero_fifthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 6).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 5).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 2).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 1).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 5).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 6).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 7).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 8).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 9).derivative +
        (p.coeff 1 * Polynomial.C (1 : k)) * (q.coeff 10).derivative) =
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
  simpa only [p, q] using fifthCoefficientJacobianRow_610 hp hq hjac

/-- At scale zero the common core is constant, so the leading sextic and
decic coefficients of the degree-`10` row are differential constants. -/
theorem scaleZero_fifthCoefficientJacobianRow_610
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 5).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 2).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 1).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 5).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 6).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 7).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 8).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 9).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp6der : (p.coeff 6).derivative = 0 := by
    rw [hp6, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := fifthCoefficientJacobianRow_610 hp hq hjac
  simpa [hp6der, hq10der] using hrow

/-- Source-facing scale-zero collapse of the degree-`10` row. -/
theorem normalized610ScaleZero_fifthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 5).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 2).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 1).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 5).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 6).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 7).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 8).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 9).derivative) =
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
    scaleZero_fifthCoefficientJacobianRow_610 hp hq hjac hHdegree
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)

/-! ## Weight-twenty-five cleared defect after a square root of the core -/

/-- Strongest exact fourth residual after the constant-scale source bridge:
the cleared weight-twenty-five sextic/decic defect is a scalar times `h²⁵`.
Both the vanishing and the nonzero values of `λ` are permitted. -/
theorem scaleZero_fourthClearedDefect_exists_C_610
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda alpha gamma delta eps : k),
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
        Polynomial.C delta * (Polynomial.C t) ^ 20 ∧
      localClearedFifthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) lambda =
        Polynomial.C eps * (Polynomial.C t) ^ 25 := by
  obtain ⟨lambda, alpha, gamma, delta, hN, halpha, hgamma, hdelta⟩ :=
    scaleZero_thirdClearedDefect_exists_C_610 hp hq hD ht hH hp6 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eps, heps⟩ :=
    nonzeroFace610_fifthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  exact ⟨lambda, alpha, gamma, delta, eps, hN, halpha, hgamma, hdelta, heps⟩

/-- Aligned specialization of the weight-twenty-five defect: the five
`λ`-monomials drop. -/
theorem localClearedFifthDefect610_of_lambda_zero
    (h a5 a4 a3 a2 a1 b8 b7 b6 b5 : k[X]) :
    localClearedFifthDefect610 h a5 a4 a3 a2 a1 b8 b7 b6 b5 0 =
      -(155520 : k[X]) * a1 * h ^ 24 +
        (51840 : k[X]) * a2 * a5 * h ^ 18 +
        (285120 : k[X]) * a3 * a4 * h ^ 18 +
        (23760 : k[X]) * a3 * a5 ^ 2 * h ^ 12 -
        (124416 : k[X]) * a3 * b8 * h ^ 14 -
        (190080 : k[X]) * a4 ^ 2 * a5 * h ^ 12 -
        (89760 : k[X]) * a4 * a5 ^ 3 * h ^ 6 +
        (228096 : k[X]) * a4 * a5 * b8 * h ^ 8 -
        (108864 : k[X]) * a4 * b7 * h ^ 14 +
        (68816 : k[X]) * a5 ^ 5 -
        (107712 : k[X]) * a5 ^ 3 * b8 * h ^ 2 +
        (99792 : k[X]) * a5 ^ 2 * b7 * h ^ 8 -
        (93312 : k[X]) * a5 * b6 * h ^ 14 +
        (93312 : k[X]) * b5 * h ^ 20 := by
  simp [localClearedFifthDefect610, map_zero]

variable [IsAlgClosed k]

/-- Source-facing fourth residual packet for a normalized scale-zero
`(6,10)` pair.  The constants `λ`, `α`, `γ`, `δ`, and `ε` may vanish. -/
theorem normalized610ScaleZero_exists_fourthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda alpha gamma delta eps : k),
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
        Polynomial.C delta * (Polynomial.C t) ^ 20 ∧
      localClearedFifthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          lambda =
        Polynomial.C eps * (Polynomial.C t) ^ 25 := by
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
  obtain ⟨lambda, alpha, gamma, delta, eps, hN, halpha, hgamma, hdelta, heps⟩ :=
    scaleZero_fourthClearedDefect_exists_C_610 hp hq hD ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  exact ⟨t, lambda, alpha, gamma, delta, eps, ht, hHsq,
    by simpa only [p, q] using hN,
    by simpa only [p, q] using halpha,
    by simpa only [p, q] using hgamma,
    by simpa only [p, q] using hdelta,
    by simpa only [p, q] using heps⟩

/-- At scale zero the weight-twenty-five defect is a literal ground-field
constant. -/
theorem normalized610ScaleZero_fourthClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda eps : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedFifthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          lambda =
        Polynomial.C eps := by
  obtain ⟨t, lambda, _alpha, _gamma, _delta, eps, ht, hHsq, _hN, _hM, _hT, _hU, hV⟩ :=
    normalized610ScaleZero_exists_fourthClearedDefect hsource
  refine ⟨t, lambda, eps * t ^ 25, ht, hHsq, ?_⟩
  have hconst :
      localClearedFifthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          lambda =
        Polynomial.C (eps * t ^ 25) := by
    rw [hV, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eps (t ^ 25)).symm
  exact hconst

/-- Newton degree of the fourth cleared sextic/decic defect at scale zero. -/
theorem normalized610ScaleZero_fourthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedFifthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, eps, ht, hHsq, hV⟩ :=
    normalized610ScaleZero_fourthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hV]
  exact (natDegree_C eps).le

/-- Exact fourth residual selector: `93312 q₅ h²⁰` differs from a polynomial
in the remaining fifth-defect monomials by a ground constant. -/
theorem normalized610ScaleZero_fourthSourceResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda eps : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (93312 : k[X]) * q.coeff 5 * h0 ^ 20 =
        Polynomial.C eps -
          (-(155520 : k[X]) * p.coeff 1 * h0 ^ 24 +
            (51840 : k[X]) * p.coeff 2 * p.coeff 5 * h0 ^ 18 +
            (46656 : k[X]) * Polynomial.C lambda * p.coeff 2 * h0 ^ 23 +
            (285120 : k[X]) * p.coeff 3 * p.coeff 4 * h0 ^ 18 +
            (23760 : k[X]) * p.coeff 3 * p.coeff 5 ^ 2 * h0 ^ 12 -
            (85536 : k[X]) * Polynomial.C lambda * p.coeff 3 * p.coeff 5 *
              h0 ^ 17 -
            (124416 : k[X]) * p.coeff 3 * q.coeff 8 * h0 ^ 14 -
            (190080 : k[X]) * p.coeff 4 ^ 2 * p.coeff 5 * h0 ^ 12 -
            (42768 : k[X]) * Polynomial.C lambda * p.coeff 4 ^ 2 * h0 ^ 17 -
            (89760 : k[X]) * p.coeff 4 * p.coeff 5 ^ 3 * h0 ^ 6 +
            (121176 : k[X]) * Polynomial.C lambda * p.coeff 4 *
              p.coeff 5 ^ 2 * h0 ^ 11 +
            (228096 : k[X]) * p.coeff 4 * p.coeff 5 * q.coeff 8 * h0 ^ 8 -
            (108864 : k[X]) * p.coeff 4 * q.coeff 7 * h0 ^ 14 +
            (68816 : k[X]) * p.coeff 5 ^ 5 -
            (38709 : k[X]) * Polynomial.C lambda * p.coeff 5 ^ 4 * h0 ^ 5 -
            (107712 : k[X]) * p.coeff 5 ^ 3 * q.coeff 8 * h0 ^ 2 +
            (99792 : k[X]) * p.coeff 5 ^ 2 * q.coeff 7 * h0 ^ 8 -
            (93312 : k[X]) * p.coeff 5 * q.coeff 6 * h0 ^ 14) := by
  dsimp only
  obtain ⟨t, lambda, eps, ht, hHsq, hV⟩ :=
    normalized610ScaleZero_fourthClearedDefect_exists_C hsource
  refine ⟨t, lambda, eps, ht, hHsq, ?_⟩
  simp only [localClearedFifthDefect610] at hV
  linear_combination hV

/-- Aligned/nonzero split of the scale-zero fourth cleared defect: it
vanishes, or it is a nonzero ground-field constant. -/
theorem normalized610ScaleZero_fourthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let V :=
        localClearedFifthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          lambda
      V = 0 ∨ ∃ eps : k, eps ≠ 0 ∧ V = Polynomial.C eps := by
  dsimp only
  obtain ⟨t, lambda, eps, ht, hHsq, hV⟩ :=
    normalized610ScaleZero_fourthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  by_cases heps : eps = 0
  · left
    simpa only [heps, Polynomial.C_0] using hV
  · exact Or.inr ⟨eps, heps, hV⟩

/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-twenty-five defect. -/
theorem normalized610ScaleZero_fourthClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda eps : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9
      let V :=
        localClearedFifthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      V = Polynomial.C eps ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (eps = 0 ∧ V = 0 ∨
        eps ≠ 0 ∧ V = Polynomial.C eps) := by
  dsimp only
  obtain ⟨t, lambda, _alpha, _gamma, _delta, eps0, ht, hHsq, hN, _hM, _hT, _hU, hVpow⟩ :=
    normalized610ScaleZero_exists_fourthClearedDefect hsource
  let eps : k := eps0 * t ^ 25
  have hV :
      localClearedFifthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          lambda =
        Polynomial.C eps := by
    rw [hVpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eps0 (t ^ 25)).symm
  refine ⟨t, lambda, eps, ht, hHsq, hN, hV, ?_, ?_⟩
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
  · by_cases heps : eps = 0
    · left
      refine ⟨heps, ?_⟩
      simpa only [heps, Polynomial.C_0] using hV
    · exact Or.inr ⟨heps, hV⟩

/-- Aligned branch `N = 0`: the weight-twenty-five defect is still a ground
constant, now with `λ = 0`. -/
theorem normalized610ScaleZero_fourthClearedDefect_of_aligned
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (haligned :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t eps : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedFifthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          0 =
        Polynomial.C eps := by
  obtain ⟨t, lambda, _alpha, _gamma, _delta, eps0, ht, hHsq, hN, _hM, _hT, _hU, hVpow⟩ :=
    normalized610ScaleZero_exists_fourthClearedDefect hsource
  have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
    pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
  have hlambda : lambda = 0 := by
    have hmul : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
      hN.symm.trans haligned
    have hC : Polynomial.C lambda = 0 :=
      (mul_eq_zero.mp hmul).resolve_right ht9
    exact Polynomial.C_eq_zero.mp hC
  refine ⟨t, eps0 * t ^ 25, ht, hHsq, ?_⟩
  have hV :
      localClearedFifthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          0 =
        Polynomial.C (eps0 * t ^ 25) := by
    rw [← hlambda, hVpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eps0 (t ^ 25)).symm
  exact hV

/-- Nonzero discriminator branch: `λ ≠ 0` and the weight-twenty-five defect is
still a ground constant. -/
theorem normalized610ScaleZero_fourthClearedDefect_of_nonzero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (hnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda eps : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedFifthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          lambda =
        Polynomial.C eps := by
  obtain ⟨t, lambda, _alpha, _gamma, _delta, eps0, ht, hHsq, hN, _hM, _hT, _hU, hVpow⟩ :=
    normalized610ScaleZero_exists_fourthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro hzero
    apply hnonzero
    simpa only [hzero, Polynomial.C_0, zero_mul] using hN
  refine ⟨t, lambda, eps0 * t ^ 25, ht, hlambda, hHsq, hN, ?_⟩
  have hV :
      localClearedFifthDefect610 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          lambda =
        Polynomial.C (eps0 * t ^ 25) := by
    rw [hVpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eps0 (t ^ 25)).symm
  exact hV

end ScaleZeroFourthDefect610

#print axioms normalized610ScaleZero_fifthCoefficientJacobianRow
#print axioms scaleZero_fifthCoefficientJacobianRow_610
#print axioms normalized610ScaleZero_fifthCoefficientJacobianRow_collapsed
#print axioms scaleZero_fourthClearedDefect_exists_C_610
#print axioms localClearedFifthDefect610_of_lambda_zero
#print axioms normalized610ScaleZero_exists_fourthClearedDefect
#print axioms normalized610ScaleZero_fourthClearedDefect_exists_C
#print axioms normalized610ScaleZero_fourthClearedDefect_natDegree_le_zero
#print axioms normalized610ScaleZero_fourthSourceResidual
#print axioms normalized610ScaleZero_fourthClearedDefectFirstFace
#print axioms normalized610ScaleZero_fourthClearedDefectBranches
#print axioms normalized610ScaleZero_fourthClearedDefect_of_aligned
#print axioms normalized610ScaleZero_fourthClearedDefect_of_nonzero

end Max11DegreeRoutes
