import LowScale610ScaleZeroFifthDefect
import LowScale610ScaleTwoSeventhFace

/-! # Scale-zero sixth cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `LowScale610ScaleZeroFifthDefect` on the constant core
`H = (C t)²`.  The fifth packet already forces the discriminator `N` and
the weight-thirty defect `W` to ground constants.  This file consumes
the next unused Keller coefficient, the degree-`8` Jacobian row

```
(p₆)' (3 q₃) + (p₅)' (4 q₄) + (p₄)' (5 q₅) + (p₃)' (6 q₆) + (p₂)' (7 q₇)
  + (p₁)' (8 q₈) + (p₀)' (9 q₉)
  - (6 p₆) q₃' - (5 p₅) q₄' - (4 p₄) q₅' - (3 p₃) q₆' - (2 p₂) q₇'
  - (1 p₁) q₈' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is
`9 L E' + 8 P D' + 7 Q C' + 6 R B' + 5 S A' - D P' - 2 C Q' - 3 B R'
- 4 A S' - 6 U' = 0`.  The corresponding first integral clears to the
weight-thirty-five polynomial defect `X`, and at scale zero that defect
is again a ground-field constant.

No total-degree or twice-prime theorem is used.  A constant scale has no
finite root, so the scale-two seventh-face jet is unavailable.  Both the
vanishing and the nonzero constant branches of `λ` and of `X` are kept.
The packet does not close the leaf: unused Jacobian coefficients start at
degree `7`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ScaleZeroSixthDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/

/-- Source-facing degree-`8` Jacobian row of a normalized scale-zero
`(6,10)` pair. -/
theorem normalized610ScaleZero_seventhCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 6).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 5).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 4).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 3).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 2).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 1).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 0).derivative * (q.coeff 9 * Polynomial.C (9 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 3).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 4).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 5).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 6).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 7).derivative +
        (p.coeff 1 * Polynomial.C (1 : k)) * (q.coeff 8).derivative) =
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
  simpa only [p, q] using seventhCoefficientJacobianRow_610 hp hq hjac

/-- At scale zero the common core is constant, so the leading sextic and
decic coefficients of the degree-`8` row are differential constants. -/
theorem scaleZero_seventhCoefficientJacobianRow_610
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 5).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 4).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 3).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 2).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 1).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 0).derivative * (q.coeff 9 * Polynomial.C (9 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 3).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 4).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 5).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 6).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 7).derivative +
        (p.coeff 1 * Polynomial.C (1 : k)) * (q.coeff 8).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp6der : (p.coeff 6).derivative = 0 := by
    rw [hp6, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := seventhCoefficientJacobianRow_610 hp hq hjac
  simpa [hp6der, hq10der] using hrow

/-- Source-facing scale-zero collapse of the degree-`8` row. -/
theorem normalized610ScaleZero_seventhCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 5).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 4).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 3).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 2).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 1).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 0).derivative * (q.coeff 9 * Polynomial.C (9 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 3).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 4).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 5).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 6).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 7).derivative +
        (p.coeff 1 * Polynomial.C (1 : k)) * (q.coeff 8).derivative) =
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
    scaleZero_seventhCoefficientJacobianRow_610 hp hq hjac hHdegree
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)

/-! ## Weight-thirty-five cleared defect after a square root of the core -/

/-- Strongest exact sixth residual after the constant-scale source bridge:
the cleared weight-thirty-five sextic/decic defect is a scalar times `h³⁵`.
Both the vanishing and the nonzero values of `λ` are permitted. -/
theorem scaleZero_sixthClearedDefect_exists_C_610
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda alpha gamma delta eps zeta eta : k),
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
        Polynomial.C eps * (Polynomial.C t) ^ 25 ∧
      localClearedSixthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
        Polynomial.C zeta * (Polynomial.C t) ^ 30 ∧
      localClearedSeventhDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 35 := by
  obtain ⟨lambda, alpha, gamma, delta, eps, zeta, hN, halpha, hgamma, hdelta,
      heps, hzeta⟩ :=
    scaleZero_fifthClearedDefect_exists_C_610 hp hq hD ht hH hp6 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace610_seventhDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  exact ⟨lambda, alpha, gamma, delta, eps, zeta, eta, hN, halpha, hgamma,
    hdelta, heps, hzeta, heta⟩

/-- Aligned specialization of the weight-thirty-five defect: the eleven
`λ`-monomials drop. -/
theorem localClearedSeventhDefect610_of_lambda_zero
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 : k[X]) :
    localClearedSeventhDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 0 =
      (7680 : k[X]) * a1 * a4 * h ^ 30 +
        (1920 : k[X]) * a1 * a5 ^ 2 * h ^ 24 -
        (4096 : k[X]) * a1 * b8 * h ^ 26 +
        (7680 : k[X]) * a2 * a3 * h ^ 30 -
        (7680 : k[X]) * a2 * a4 * a5 * h ^ 24 -
        (3200 : k[X]) * a2 * a5 ^ 3 * h ^ 18 +
        (6144 : k[X]) * a2 * a5 * b8 * h ^ 20 -
        (3584 : k[X]) * a2 * b7 * h ^ 26 -
        (3840 : k[X]) * a3 ^ 2 * a5 * h ^ 24 -
        (9600 : k[X]) * a3 * a4 ^ 2 * h ^ 24 +
        (4800 : k[X]) * a3 * a4 * a5 ^ 2 * h ^ 18 +
        (6144 : k[X]) * a3 * a4 * b8 * h ^ 20 +
        (4200 : k[X]) * a3 * a5 ^ 4 * h ^ 12 -
        (7680 : k[X]) * a3 * a5 ^ 2 * b8 * h ^ 14 +
        (5376 : k[X]) * a3 * a5 * b7 * h ^ 20 -
        (3072 : k[X]) * a3 * b6 * h ^ 26 +
        (6400 : k[X]) * a4 ^ 3 * a5 * h ^ 18 -
        (7680 : k[X]) * a4 ^ 2 * a5 * b8 * h ^ 14 +
        (2688 : k[X]) * a4 ^ 2 * b7 * h ^ 20 -
        (5040 : k[X]) * a4 * a5 ^ 5 * h ^ 6 +
        (8960 : k[X]) * a4 * a5 ^ 3 * b8 * h ^ 8 -
        (6720 : k[X]) * a4 * a5 ^ 2 * b7 * h ^ 14 +
        (4608 : k[X]) * a4 * a5 * b6 * h ^ 20 -
        (2560 : k[X]) * a4 * b5 * h ^ 26 +
        (1320 : k[X]) * a5 ^ 7 -
        (2016 : k[X]) * a5 ^ 5 * b8 * h ^ 2 +
        (1960 : k[X]) * a5 ^ 4 * b7 * h ^ 8 -
        (1920 : k[X]) * a5 ^ 3 * b6 * h ^ 14 +
        (1920 : k[X]) * a5 ^ 2 * b5 * h ^ 20 -
        (2048 : k[X]) * a5 * b4 * h ^ 26 +
        (3072 : k[X]) * b3 * h ^ 32 := by
  simp [localClearedSeventhDefect610, map_zero]

variable [IsAlgClosed k]

/-- Source-facing sixth residual packet for a normalized scale-zero
`(6,10)` pair.  The constants `λ`, `α`, `γ`, `δ`, `ε`, `ζ`, and `η`
may vanish. -/
theorem normalized610ScaleZero_exists_sixthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda alpha gamma delta eps zeta eta : k),
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
        Polynomial.C eps * (Polynomial.C t) ^ 25 ∧
      localClearedSixthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C zeta * (Polynomial.C t) ^ 30 ∧
      localClearedSeventhDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 35 := by
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
  obtain ⟨lambda, alpha, gamma, delta, eps, zeta, eta, hN, halpha, hgamma,
      hdelta, heps, hzeta, heta⟩ :=
    scaleZero_sixthClearedDefect_exists_C_610 hp hq hD ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  exact ⟨t, lambda, alpha, gamma, delta, eps, zeta, eta, ht, hHsq,
    by simpa only [p, q] using hN,
    by simpa only [p, q] using halpha,
    by simpa only [p, q] using hgamma,
    by simpa only [p, q] using hdelta,
    by simpa only [p, q] using heps,
    by simpa only [p, q] using hzeta,
    by simpa only [p, q] using heta⟩

/-- At scale zero the weight-thirty-five defect is a literal ground-field
constant. -/
theorem normalized610ScaleZero_sixthClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedSeventhDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C eta := by
  obtain ⟨t, lambda, _alpha, _gamma, _delta, _eps, _zeta, eta, ht, hHsq, _hN,
      _hM, _hT, _hU, _hV, _hW, hX⟩ :=
    normalized610ScaleZero_exists_sixthClearedDefect hsource
  refine ⟨t, lambda, eta * t ^ 35, ht, hHsq, ?_⟩
  have hconst :
      localClearedSeventhDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C (eta * t ^ 35) := by
    rw [hX, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta (t ^ 35)).symm
  exact hconst

/-- Newton degree of the sixth cleared sextic/decic defect at scale zero. -/
theorem normalized610ScaleZero_sixthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedSeventhDefect610 (Polynomial.C t)
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
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, eta, ht, hHsq, hX⟩ :=
    normalized610ScaleZero_sixthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hX]
  exact (natDegree_C eta).le

/-- Exact sixth residual selector: `3072 q₃ h³²` differs from a polynomial
in the remaining seventh-defect monomials by a ground constant. -/
theorem normalized610ScaleZero_sixthSourceResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (3072 : k[X]) * q.coeff 3 * h0 ^ 32 =
        Polynomial.C eta -
          ((1536 : k[X]) * Polynomial.C lambda * p.coeff 0 * h0 ^ 35 +
            (7680 : k[X]) * p.coeff 1 * p.coeff 4 * h0 ^ 30 +
            (1920 : k[X]) * p.coeff 1 * p.coeff 5 ^ 2 * h0 ^ 24 -
            (2304 : k[X]) * Polynomial.C lambda * p.coeff 1 * p.coeff 5 *
              h0 ^ 29 -
            (4096 : k[X]) * p.coeff 1 * q.coeff 8 * h0 ^ 26 +
            (7680 : k[X]) * p.coeff 2 * p.coeff 3 * h0 ^ 30 -
            (7680 : k[X]) * p.coeff 2 * p.coeff 4 * p.coeff 5 * h0 ^ 24 -
            (2304 : k[X]) * Polynomial.C lambda * p.coeff 2 * p.coeff 4 *
              h0 ^ 29 -
            (3200 : k[X]) * p.coeff 2 * p.coeff 5 ^ 3 * h0 ^ 18 +
            (2880 : k[X]) * Polynomial.C lambda * p.coeff 2 *
              p.coeff 5 ^ 2 * h0 ^ 23 +
            (6144 : k[X]) * p.coeff 2 * p.coeff 5 * q.coeff 8 * h0 ^ 20 -
            (3584 : k[X]) * p.coeff 2 * q.coeff 7 * h0 ^ 26 -
            (3840 : k[X]) * p.coeff 3 ^ 2 * p.coeff 5 * h0 ^ 24 -
            (1152 : k[X]) * Polynomial.C lambda * p.coeff 3 ^ 2 * h0 ^ 29 -
            (9600 : k[X]) * p.coeff 3 * p.coeff 4 ^ 2 * h0 ^ 24 +
            (4800 : k[X]) * p.coeff 3 * p.coeff 4 * p.coeff 5 ^ 2 *
              h0 ^ 18 +
            (5760 : k[X]) * Polynomial.C lambda * p.coeff 3 * p.coeff 4 *
              p.coeff 5 * h0 ^ 23 +
            (6144 : k[X]) * p.coeff 3 * p.coeff 4 * q.coeff 8 * h0 ^ 20 +
            (4200 : k[X]) * p.coeff 3 * p.coeff 5 ^ 4 * h0 ^ 12 -
            (3360 : k[X]) * Polynomial.C lambda * p.coeff 3 *
              p.coeff 5 ^ 3 * h0 ^ 17 -
            (7680 : k[X]) * p.coeff 3 * p.coeff 5 ^ 2 * q.coeff 8 *
              h0 ^ 14 +
            (5376 : k[X]) * p.coeff 3 * p.coeff 5 * q.coeff 7 * h0 ^ 20 -
            (3072 : k[X]) * p.coeff 3 * q.coeff 6 * h0 ^ 26 +
            (6400 : k[X]) * p.coeff 4 ^ 3 * p.coeff 5 * h0 ^ 18 +
            (960 : k[X]) * Polynomial.C lambda * p.coeff 4 ^ 3 * h0 ^ 23 -
            (5040 : k[X]) * Polynomial.C lambda * p.coeff 4 ^ 2 *
              p.coeff 5 ^ 2 * h0 ^ 17 -
            (7680 : k[X]) * p.coeff 4 ^ 2 * p.coeff 5 * q.coeff 8 *
              h0 ^ 14 +
            (2688 : k[X]) * p.coeff 4 ^ 2 * q.coeff 7 * h0 ^ 20 -
            (5040 : k[X]) * p.coeff 4 * p.coeff 5 ^ 5 * h0 ^ 6 +
            (3780 : k[X]) * Polynomial.C lambda * p.coeff 4 *
              p.coeff 5 ^ 4 * h0 ^ 11 +
            (8960 : k[X]) * p.coeff 4 * p.coeff 5 ^ 3 * q.coeff 8 *
              h0 ^ 8 -
            (6720 : k[X]) * p.coeff 4 * p.coeff 5 ^ 2 * q.coeff 7 *
              h0 ^ 14 +
            (4608 : k[X]) * p.coeff 4 * p.coeff 5 * q.coeff 6 * h0 ^ 20 -
            (2560 : k[X]) * p.coeff 4 * q.coeff 5 * h0 ^ 26 +
            (1320 : k[X]) * p.coeff 5 ^ 7 -
            (693 : k[X]) * Polynomial.C lambda * p.coeff 5 ^ 6 * h0 ^ 5 -
            (2016 : k[X]) * p.coeff 5 ^ 5 * q.coeff 8 * h0 ^ 2 +
            (1960 : k[X]) * p.coeff 5 ^ 4 * q.coeff 7 * h0 ^ 8 -
            (1920 : k[X]) * p.coeff 5 ^ 3 * q.coeff 6 * h0 ^ 14 +
            (1920 : k[X]) * p.coeff 5 ^ 2 * q.coeff 5 * h0 ^ 20 -
            (2048 : k[X]) * p.coeff 5 * q.coeff 4 * h0 ^ 26) := by
  dsimp only
  obtain ⟨t, lambda, eta, ht, hHsq, hX⟩ :=
    normalized610ScaleZero_sixthClearedDefect_exists_C hsource
  refine ⟨t, lambda, eta, ht, hHsq, ?_⟩
  simp only [localClearedSeventhDefect610] at hX
  linear_combination hX

/-- Aligned/nonzero split of the scale-zero sixth cleared defect: it
vanishes, or it is a nonzero ground-field constant. -/
theorem normalized610ScaleZero_sixthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let X :=
        localClearedSeventhDefect610 (Polynomial.C t)
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
          lambda
      X = 0 ∨ ∃ eta : k, eta ≠ 0 ∧ X = Polynomial.C eta := by
  dsimp only
  obtain ⟨t, lambda, eta, ht, hHsq, hX⟩ :=
    normalized610ScaleZero_sixthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  by_cases heta : eta = 0
  · left
    simpa only [heta, Polynomial.C_0] using hX
  · exact Or.inr ⟨eta, heta, hX⟩

/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-thirty-five defect. -/
theorem normalized610ScaleZero_sixthClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9
      let X :=
        localClearedSeventhDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      X = Polynomial.C eta ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (eta = 0 ∧ X = 0 ∨
        eta ≠ 0 ∧ X = Polynomial.C eta) := by
  dsimp only
  obtain ⟨t, lambda, _alpha, _gamma, _delta, _eps, _zeta, eta0, ht, hHsq, hN,
      _hM, _hT, _hU, _hV, _hW, hXpow⟩ :=
    normalized610ScaleZero_exists_sixthClearedDefect hsource
  let eta : k := eta0 * t ^ 35
  have hX :
      localClearedSeventhDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C eta := by
    rw [hXpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta0 (t ^ 35)).symm
  refine ⟨t, lambda, eta, ht, hHsq, hN, hX, ?_, ?_⟩
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
  · by_cases heta : eta = 0
    · left
      refine ⟨heta, ?_⟩
      simpa only [heta, Polynomial.C_0] using hX
    · exact Or.inr ⟨heta, hX⟩

/-- Aligned branch `N = 0`: the weight-thirty-five defect is still a ground
constant, now with `λ = 0`. -/
theorem normalized610ScaleZero_sixthClearedDefect_of_aligned
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (haligned :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedSeventhDefect610 (Polynomial.C t)
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
          0 =
        Polynomial.C eta := by
  obtain ⟨t, lambda, _alpha, _gamma, _delta, _eps, _zeta, eta0, ht, hHsq, hN,
      _hM, _hT, _hU, _hV, _hW, hXpow⟩ :=
    normalized610ScaleZero_exists_sixthClearedDefect hsource
  have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
    pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
  have hlambda : lambda = 0 := by
    have hmul : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
      hN.symm.trans haligned
    have hC : Polynomial.C lambda = 0 :=
      (mul_eq_zero.mp hmul).resolve_right ht9
    exact Polynomial.C_eq_zero.mp hC
  refine ⟨t, eta0 * t ^ 35, ht, hHsq, ?_⟩
  have hX :
      localClearedSeventhDefect610 (Polynomial.C t)
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
          0 =
        Polynomial.C (eta0 * t ^ 35) := by
    rw [← hlambda, hXpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta0 (t ^ 35)).symm
  exact hX

/-- Nonzero discriminator branch: `λ ≠ 0` and the weight-thirty-five defect
is still a ground constant. -/
theorem normalized610ScaleZero_sixthClearedDefect_of_nonzero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (hnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedSeventhDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C eta := by
  obtain ⟨t, lambda, _alpha, _gamma, _delta, _eps, _zeta, eta0, ht, hHsq, hN,
      _hM, _hT, _hU, _hV, _hW, hXpow⟩ :=
    normalized610ScaleZero_exists_sixthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro hzero
    apply hnonzero
    simpa only [hzero, Polynomial.C_0, zero_mul] using hN
  refine ⟨t, lambda, eta0 * t ^ 35, ht, hlambda, hHsq, hN, ?_⟩
  have hX :
      localClearedSeventhDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C (eta0 * t ^ 35) := by
    rw [hXpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta0 (t ^ 35)).symm
  exact hX

end ScaleZeroSixthDefect610

#print axioms normalized610ScaleZero_seventhCoefficientJacobianRow
#print axioms scaleZero_seventhCoefficientJacobianRow_610
#print axioms normalized610ScaleZero_seventhCoefficientJacobianRow_collapsed
#print axioms scaleZero_sixthClearedDefect_exists_C_610
#print axioms localClearedSeventhDefect610_of_lambda_zero
#print axioms normalized610ScaleZero_exists_sixthClearedDefect
#print axioms normalized610ScaleZero_sixthClearedDefect_exists_C
#print axioms normalized610ScaleZero_sixthClearedDefect_natDegree_le_zero
#print axioms normalized610ScaleZero_sixthSourceResidual
#print axioms normalized610ScaleZero_sixthClearedDefectFirstFace
#print axioms normalized610ScaleZero_sixthClearedDefectBranches
#print axioms normalized610ScaleZero_sixthClearedDefect_of_aligned
#print axioms normalized610ScaleZero_sixthClearedDefect_of_nonzero

end Max11DegreeRoutes
