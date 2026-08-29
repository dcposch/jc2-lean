import LowScale610ScaleZeroFourthDefect
import LowScale610ScaleTwoSixthFace

/-! # Scale-zero fifth cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroFourthDefectScratch` on the constant core
`H = (C t)²`.  The fourth packet already forces the discriminator `N` and
the weight-twenty-five defect `V` to ground constants.  This file consumes
the next unused Keller coefficient, the degree-`9` Jacobian row
```
(p₆)' (4 q₄) + (p₅)' (5 q₅) + (p₄)' (6 q₆) + (p₃)' (7 q₇) + (p₂)' (8 q₈)
  + (p₁)' (9 q₉) + (p₀)' (10 q₁₀)
  - (6 p₆) q₄' - (5 p₅) q₅' - (4 p₄) q₆' - (3 p₃) q₇' - (2 p₂) q₈'
  - (1 p₁) q₉' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is
`10 E' + 9 L D' + 8 P C' + 7 Q B' + 6 R A' - 2 C P' - 3 B Q' - 4 A R'
- 6 T' = 0`.  The corresponding first integral clears to the weight-thirty
polynomial defect `W`, and at scale zero that defect is again a ground-field
constant.

No total-degree or twice-prime theorem is used.  A constant scale has no
finite root, so the scale-two sixth-face jet is unavailable.  Both the
vanishing and the nonzero constant branches of `λ` and of `W` are kept.
The packet does not close the leaf: unused Jacobian coefficients start at
degree `8`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ScaleZeroFifthDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/

/-- Source-facing degree-`9` Jacobian row of a normalized scale-zero
`(6,10)` pair. -/
theorem normalized610ScaleZero_sixthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 6).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 5).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 4).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 3).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 2).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 1).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 0).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 4).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 5).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 6).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 7).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 8).derivative +
        (p.coeff 1 * Polynomial.C (1 : k)) * (q.coeff 9).derivative) =
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
  simpa only [p, q] using sixthCoefficientJacobianRow_610 hp hq hjac

/-- At scale zero the common core is constant, so the leading sextic and
decic coefficients of the degree-`9` row are differential constants. -/
theorem scaleZero_sixthCoefficientJacobianRow_610
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 5).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 4).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 3).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 2).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 1).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 0).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 4).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 5).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 6).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 7).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 8).derivative +
        (p.coeff 1 * Polynomial.C (1 : k)) * (q.coeff 9).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp6der : (p.coeff 6).derivative = 0 := by
    rw [hp6, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := sixthCoefficientJacobianRow_610 hp hq hjac
  simpa [hp6der, hq10der] using hrow

/-- Source-facing scale-zero collapse of the degree-`9` row. -/
theorem normalized610ScaleZero_sixthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 5).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 4).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 3).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 2).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 1).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 0).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 4).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 5).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 6).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 7).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 8).derivative +
        (p.coeff 1 * Polynomial.C (1 : k)) * (q.coeff 9).derivative) =
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
    scaleZero_sixthCoefficientJacobianRow_610 hp hq hjac hHdegree
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)

/-! ## Weight-thirty cleared defect after a square root of the core -/

/-- Strongest exact fifth residual after the constant-scale source bridge:
the cleared weight-thirty sextic/decic defect is a scalar times `h³⁰`.
Both the vanishing and the nonzero values of `λ` are permitted. -/
theorem scaleZero_fifthClearedDefect_exists_C_610
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda alpha gamma delta eps zeta : k),
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
        Polynomial.C zeta * (Polynomial.C t) ^ 30 := by
  obtain ⟨lambda, alpha, gamma, delta, eps, hN, halpha, hgamma, hdelta, heps⟩ :=
    scaleZero_fourthClearedDefect_exists_C_610 hp hq hD ht hH hp6 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨zeta, hzeta⟩ :=
    nonzeroFace610_sixthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  exact ⟨lambda, alpha, gamma, delta, eps, zeta, hN, halpha, hgamma, hdelta,
    heps, hzeta⟩

/-- Aligned specialization of the weight-thirty defect: the seven
`λ`-monomials drop. -/
theorem localClearedSixthDefect610_of_lambda_zero
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 : k[X]) :
    localClearedSixthDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 0 =
      -(699840 : k[X]) * a0 * h ^ 30 +
        (116640 : k[X]) * a1 * a5 * h ^ 24 +
        (1166400 : k[X]) * a2 * a4 * h ^ 24 +
        (194400 : k[X]) * a2 * a5 ^ 2 * h ^ 18 -
        (559872 : k[X]) * a2 * b8 * h ^ 20 +
        (583200 : k[X]) * a3 ^ 2 * h ^ 24 -
        (1360800 : k[X]) * a3 * a4 * a5 * h ^ 18 -
        (432000 : k[X]) * a3 * a5 ^ 3 * h ^ 12 +
        (933120 : k[X]) * a3 * a5 * b8 * h ^ 14 -
        (489888 : k[X]) * a3 * b7 * h ^ 20 -
        (518400 : k[X]) * a4 ^ 3 * h ^ 18 +
        (518400 : k[X]) * a4 ^ 2 * a5 ^ 2 * h ^ 12 +
        (466560 : k[X]) * a4 ^ 2 * b8 * h ^ 14 +
        (633600 : k[X]) * a4 * a5 ^ 4 * h ^ 6 -
        (1244160 : k[X]) * a4 * a5 ^ 2 * b8 * h ^ 8 +
        (816480 : k[X]) * a4 * a5 * b7 * h ^ 14 -
        (419904 : k[X]) * a4 * b6 * h ^ 20 -
        (246400 : k[X]) * a5 ^ 6 +
        (380160 : k[X]) * a5 ^ 4 * b8 * h ^ 2 -
        (362880 : k[X]) * a5 ^ 3 * b7 * h ^ 8 +
        (349920 : k[X]) * a5 ^ 2 * b6 * h ^ 14 -
        (349920 : k[X]) * a5 * b5 * h ^ 20 +
        (419904 : k[X]) * b4 * h ^ 26 := by
  simp [localClearedSixthDefect610, map_zero]

variable [IsAlgClosed k]

/-- Source-facing fifth residual packet for a normalized scale-zero
`(6,10)` pair.  The constants `λ`, `α`, `γ`, `δ`, `ε`, and `ζ` may vanish. -/
theorem normalized610ScaleZero_exists_fifthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda alpha gamma delta eps zeta : k),
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
        Polynomial.C zeta * (Polynomial.C t) ^ 30 := by
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
  obtain ⟨lambda, alpha, gamma, delta, eps, zeta, hN, halpha, hgamma, hdelta,
      heps, hzeta⟩ :=
    scaleZero_fifthClearedDefect_exists_C_610 hp hq hD ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  exact ⟨t, lambda, alpha, gamma, delta, eps, zeta, ht, hHsq,
    by simpa only [p, q] using hN,
    by simpa only [p, q] using halpha,
    by simpa only [p, q] using hgamma,
    by simpa only [p, q] using hdelta,
    by simpa only [p, q] using heps,
    by simpa only [p, q] using hzeta⟩

/-- At scale zero the weight-thirty defect is a literal ground-field
constant. -/
theorem normalized610ScaleZero_fifthClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda zeta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
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
        Polynomial.C zeta := by
  obtain ⟨t, lambda, _alpha, _gamma, _delta, _eps, zeta, ht, hHsq, _hN, _hM,
      _hT, _hU, _hV, hW⟩ :=
    normalized610ScaleZero_exists_fifthClearedDefect hsource
  refine ⟨t, lambda, zeta * t ^ 30, ht, hHsq, ?_⟩
  have hconst :
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
        Polynomial.C (zeta * t ^ 30) := by
    rw [hW, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) zeta (t ^ 30)).symm
  exact hconst

/-- Newton degree of the fifth cleared sextic/decic defect at scale zero. -/
theorem normalized610ScaleZero_fifthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedSixthDefect610 (Polynomial.C t)
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
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, zeta, ht, hHsq, hW⟩ :=
    normalized610ScaleZero_fifthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hW]
  exact (natDegree_C zeta).le

/-- Exact fifth residual selector: `419904 q₄ h²⁶` differs from a polynomial
in the remaining sixth-defect monomials by a ground constant. -/
theorem normalized610ScaleZero_fifthSourceResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda zeta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (419904 : k[X]) * q.coeff 4 * h0 ^ 26 =
        Polynomial.C zeta -
          (-(699840 : k[X]) * p.coeff 0 * h0 ^ 30 +
            (116640 : k[X]) * p.coeff 1 * p.coeff 5 * h0 ^ 24 +
            (209952 : k[X]) * Polynomial.C lambda * p.coeff 1 * h0 ^ 29 +
            (1166400 : k[X]) * p.coeff 2 * p.coeff 4 * h0 ^ 24 +
            (194400 : k[X]) * p.coeff 2 * p.coeff 5 ^ 2 * h0 ^ 18 -
            (349920 : k[X]) * Polynomial.C lambda * p.coeff 2 * p.coeff 5 *
              h0 ^ 23 -
            (559872 : k[X]) * p.coeff 2 * q.coeff 8 * h0 ^ 20 +
            (583200 : k[X]) * p.coeff 3 ^ 2 * h0 ^ 24 -
            (1360800 : k[X]) * p.coeff 3 * p.coeff 4 * p.coeff 5 * h0 ^ 18 -
            (349920 : k[X]) * Polynomial.C lambda * p.coeff 3 * p.coeff 4 *
              h0 ^ 23 -
            (432000 : k[X]) * p.coeff 3 * p.coeff 5 ^ 3 * h0 ^ 12 +
            (466560 : k[X]) * Polynomial.C lambda * p.coeff 3 *
              p.coeff 5 ^ 2 * h0 ^ 17 +
            (933120 : k[X]) * p.coeff 3 * p.coeff 5 * q.coeff 8 * h0 ^ 14 -
            (489888 : k[X]) * p.coeff 3 * q.coeff 7 * h0 ^ 20 -
            (518400 : k[X]) * p.coeff 4 ^ 3 * h0 ^ 18 +
            (518400 : k[X]) * p.coeff 4 ^ 2 * p.coeff 5 ^ 2 * h0 ^ 12 +
            (466560 : k[X]) * Polynomial.C lambda * p.coeff 4 ^ 2 *
              p.coeff 5 * h0 ^ 17 +
            (466560 : k[X]) * p.coeff 4 ^ 2 * q.coeff 8 * h0 ^ 14 +
            (633600 : k[X]) * p.coeff 4 * p.coeff 5 ^ 4 * h0 ^ 6 -
            (570240 : k[X]) * Polynomial.C lambda * p.coeff 4 *
              p.coeff 5 ^ 3 * h0 ^ 11 -
            (1244160 : k[X]) * p.coeff 4 * p.coeff 5 ^ 2 * q.coeff 8 *
              h0 ^ 8 +
            (816480 : k[X]) * p.coeff 4 * p.coeff 5 * q.coeff 7 * h0 ^ 14 -
            (419904 : k[X]) * p.coeff 4 * q.coeff 6 * h0 ^ 20 -
            (246400 : k[X]) * p.coeff 5 ^ 6 +
            (133056 : k[X]) * Polynomial.C lambda * p.coeff 5 ^ 5 * h0 ^ 5 +
            (380160 : k[X]) * p.coeff 5 ^ 4 * q.coeff 8 * h0 ^ 2 -
            (362880 : k[X]) * p.coeff 5 ^ 3 * q.coeff 7 * h0 ^ 8 +
            (349920 : k[X]) * p.coeff 5 ^ 2 * q.coeff 6 * h0 ^ 14 -
            (349920 : k[X]) * p.coeff 5 * q.coeff 5 * h0 ^ 20) := by
  dsimp only
  obtain ⟨t, lambda, zeta, ht, hHsq, hW⟩ :=
    normalized610ScaleZero_fifthClearedDefect_exists_C hsource
  refine ⟨t, lambda, zeta, ht, hHsq, ?_⟩
  simp only [localClearedSixthDefect610] at hW
  linear_combination hW

/-- Aligned/nonzero split of the scale-zero fifth cleared defect: it
vanishes, or it is a nonzero ground-field constant. -/
theorem normalized610ScaleZero_fifthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let W :=
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
          lambda
      W = 0 ∨ ∃ zeta : k, zeta ≠ 0 ∧ W = Polynomial.C zeta := by
  dsimp only
  obtain ⟨t, lambda, zeta, ht, hHsq, hW⟩ :=
    normalized610ScaleZero_fifthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  by_cases hzeta : zeta = 0
  · left
    simpa only [hzeta, Polynomial.C_0] using hW
  · exact Or.inr ⟨zeta, hzeta, hW⟩

/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-thirty defect. -/
theorem normalized610ScaleZero_fifthClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda zeta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9
      let W :=
        localClearedSixthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      W = Polynomial.C zeta ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (zeta = 0 ∧ W = 0 ∨
        zeta ≠ 0 ∧ W = Polynomial.C zeta) := by
  dsimp only
  obtain ⟨t, lambda, _alpha, _gamma, _delta, _eps, zeta0, ht, hHsq, hN, _hM,
      _hT, _hU, _hV, hWpow⟩ :=
    normalized610ScaleZero_exists_fifthClearedDefect hsource
  let zeta : k := zeta0 * t ^ 30
  have hW :
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
        Polynomial.C zeta := by
    rw [hWpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) zeta0 (t ^ 30)).symm
  refine ⟨t, lambda, zeta, ht, hHsq, hN, hW, ?_, ?_⟩
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
  · by_cases hzeta : zeta = 0
    · left
      refine ⟨hzeta, ?_⟩
      simpa only [hzeta, Polynomial.C_0] using hW
    · exact Or.inr ⟨hzeta, hW⟩

/-- Aligned branch `N = 0`: the weight-thirty defect is still a ground
constant, now with `λ = 0`. -/
theorem normalized610ScaleZero_fifthClearedDefect_of_aligned
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (haligned :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t zeta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
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
          0 =
        Polynomial.C zeta := by
  obtain ⟨t, lambda, _alpha, _gamma, _delta, _eps, zeta0, ht, hHsq, hN, _hM,
      _hT, _hU, _hV, hWpow⟩ :=
    normalized610ScaleZero_exists_fifthClearedDefect hsource
  have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
    pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
  have hlambda : lambda = 0 := by
    have hmul : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
      hN.symm.trans haligned
    have hC : Polynomial.C lambda = 0 :=
      (mul_eq_zero.mp hmul).resolve_right ht9
    exact Polynomial.C_eq_zero.mp hC
  refine ⟨t, zeta0 * t ^ 30, ht, hHsq, ?_⟩
  have hW :
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
          0 =
        Polynomial.C (zeta0 * t ^ 30) := by
    rw [← hlambda, hWpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) zeta0 (t ^ 30)).symm
  exact hW

/-- Nonzero discriminator branch: `λ ≠ 0` and the weight-thirty defect is
still a ground constant. -/
theorem normalized610ScaleZero_fifthClearedDefect_of_nonzero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (hnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda zeta : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
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
        Polynomial.C zeta := by
  obtain ⟨t, lambda, _alpha, _gamma, _delta, _eps, zeta0, ht, hHsq, hN, _hM,
      _hT, _hU, _hV, hWpow⟩ :=
    normalized610ScaleZero_exists_fifthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro hzero
    apply hnonzero
    simpa only [hzero, Polynomial.C_0, zero_mul] using hN
  refine ⟨t, lambda, zeta0 * t ^ 30, ht, hlambda, hHsq, hN, ?_⟩
  have hW :
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
        Polynomial.C (zeta0 * t ^ 30) := by
    rw [hWpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) zeta0 (t ^ 30)).symm
  exact hW

end ScaleZeroFifthDefect610

#print axioms normalized610ScaleZero_sixthCoefficientJacobianRow
#print axioms scaleZero_sixthCoefficientJacobianRow_610
#print axioms normalized610ScaleZero_sixthCoefficientJacobianRow_collapsed
#print axioms scaleZero_fifthClearedDefect_exists_C_610
#print axioms localClearedSixthDefect610_of_lambda_zero
#print axioms normalized610ScaleZero_exists_fifthClearedDefect
#print axioms normalized610ScaleZero_fifthClearedDefect_exists_C
#print axioms normalized610ScaleZero_fifthClearedDefect_natDegree_le_zero
#print axioms normalized610ScaleZero_fifthSourceResidual
#print axioms normalized610ScaleZero_fifthClearedDefectFirstFace
#print axioms normalized610ScaleZero_fifthClearedDefectBranches
#print axioms normalized610ScaleZero_fifthClearedDefect_of_aligned
#print axioms normalized610ScaleZero_fifthClearedDefect_of_nonzero

end Max11DegreeRoutes
