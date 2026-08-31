import LowScale610ScaleZeroSixthDefect
import LowScale610ScaleTwoEighthFace

/-! # Scale-zero seventh cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `LowScale610ScaleZeroSixthDefect` on the constant core
`H = (C t)²`.  The sixth packet already forces the discriminator `N` and
the weight-thirty-five defect `X` to ground constants.  This file consumes
the next unused Keller coefficient, the degree-`7` Jacobian row

```
(p₆)' (2 q₂) + (p₅)' (3 q₃) + (p₄)' (4 q₄) + (p₃)' (5 q₅) + (p₂)' (6 q₆)
  + (p₁)' (7 q₇) + (p₀)' (8 q₈)
  - (6 p₆) q₂' - (5 p₅) q₃' - (4 p₄) q₄' - (3 p₃) q₅' - (2 p₂) q₆'
  - (1 p₁) q₇' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is
`8 P E' + 7 Q D' + 6 R C' + 5 S B' + 4 T A' - D Q' - 2 C R' - 3 B S'
- 4 A T' - 6 V' = 0`.  The corresponding first integral clears to the
weight-forty polynomial defect `Y`, and at scale zero that defect is
again a ground-field constant.

No total-degree or twice-prime theorem is used.  A constant scale has no
finite root, so the scale-two eighth-face jet is unavailable.  Both the
vanishing and the nonzero constant branches of `λ` and of `Y` are kept.
The packet does not close the leaf: unused Jacobian coefficients start at
degree `6`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ScaleZeroSeventhDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/

/-- Source-facing degree-`7` Jacobian row of a normalized scale-zero
`(6,10)` pair. -/
theorem normalized610ScaleZero_eighthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 6).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 5).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 2).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 3).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 4).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 5).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 6).derivative +
        (p.coeff 1 * Polynomial.C (1 : k)) * (q.coeff 7).derivative) =
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
  simpa only [p, q] using eighthCoefficientJacobianRow_610 hp hq hjac

/-- At scale zero the common core is constant, so the leading sextic
coefficient of the degree-`7` row is a differential constant. -/
theorem scaleZero_eighthCoefficientJacobianRow_610
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 5).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 2).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 3).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 4).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 5).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 6).derivative +
        (p.coeff 1 * Polynomial.C (1 : k)) * (q.coeff 7).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp6der : (p.coeff 6).derivative = 0 := by
    rw [hp6, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := eighthCoefficientJacobianRow_610 hp hq hjac
  simpa [hp6der, hq10der] using hrow

/-- Source-facing scale-zero collapse of the degree-`7` row. -/
theorem normalized610ScaleZero_eighthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 5).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 4).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 3).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 2).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 1).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 0).derivative * (q.coeff 8 * Polynomial.C (8 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 2).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 3).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 4).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 5).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 6).derivative +
        (p.coeff 1 * Polynomial.C (1 : k)) * (q.coeff 7).derivative) =
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
    scaleZero_eighthCoefficientJacobianRow_610 hp hq hjac hHdegree
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)

/-! ## Weight-forty cleared defect after a square root of the core -/

section Depression610Eighth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z²` coefficient. -/
def depressedV610 (h r b9 b8 b7 b6 b5 b4 b3 b2 : F) : F :=
  45 * r ^ 8 - 36 * (b9 / h ^ 9) * r ^ 7 +
    28 * (b8 / h ^ 8) * r ^ 6 - 21 * (b7 / h ^ 7) * r ^ 5 +
    15 * (b6 / h ^ 6) * r ^ 4 - 10 * (b5 / h ^ 5) * r ^ 3 +
    6 * (b4 / h ^ 4) * r ^ 2 - 3 * (b3 / h ^ 3) * r + b2 / h ^ 2

/-- First residual of the degree-`7` row.  Equivalent to
`V - (4/3) α E - (7/6) β D - γ C - (5/6) δ B - (2/3) ε A
- (10/9) A E - (10/9) B D - (5/9) C² + (5/27) A B² + (5/27) A² C
- (5/243) A⁴ + (4/81) α A³ - (4/9) α A C - (2/9) α B² - (7/36) β A B
- (3/4) L A D - (3/4) L B C + (3/16) L A² B`
on the second- through sixth-face integrals. -/
def etaResidual610 (L A B C0 D0 E0 P Q R S0 T0 V0 : F) : F :=
  V0 - (4 / 3 : F) * alphaResidual610 A P * E0 -
    (7 / 6 : F) * betaResidual610 L A B Q * D0 -
    gammaResidual610 L A B C0 P R * C0 -
    (5 / 6 : F) * deltaResidual610 L A B C0 D0 P Q S0 * B -
    (2 / 3 : F) * epsilonResidual610 L A B C0 D0 E0 P Q R T0 * A -
    (10 / 9 : F) * A * E0 - (10 / 9 : F) * B * D0 -
    (5 / 9 : F) * C0 ^ 2 + (5 / 27 : F) * A * B ^ 2 +
    (5 / 27 : F) * A ^ 2 * C0 - (5 / 243 : F) * A ^ 4 +
    (4 / 81 : F) * alphaResidual610 A P * A ^ 3 -
    (4 / 9 : F) * alphaResidual610 A P * A * C0 -
    (2 / 9 : F) * alphaResidual610 A P * B ^ 2 -
    (7 / 36 : F) * betaResidual610 L A B Q * A * B -
    (3 / 4 : F) * L * A * D0 - (3 / 4 : F) * L * B * C0 +
    (3 / 16 : F) * L * A ^ 2 * B

/-- Polynomial numerator of `118098 h⁴⁰ η` on the ninth-power face. -/
def localClearedEighthDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 : F[X]) (lambda : F) : F[X] :=
  (262440 : F[X]) * a0 * a4 * h ^ 36 +
    (87480 : F[X]) * a0 * a5 ^ 2 * h ^ 30 -
    (78732 : F[X]) * Polynomial.C lambda * a0 * a5 * h ^ 35 -
    (157464 : F[X]) * a0 * b8 * h ^ 32 +
    (262440 : F[X]) * a1 * a3 * h ^ 36 -
    (218700 : F[X]) * a1 * a4 * a5 * h ^ 30 -
    (78732 : F[X]) * Polynomial.C lambda * a1 * a4 * h ^ 35 -
    (119070 : F[X]) * a1 * a5 ^ 3 * h ^ 24 +
    (91854 : F[X]) * Polynomial.C lambda * a1 * a5 ^ 2 * h ^ 29 +
    (209952 : F[X]) * a1 * a5 * b8 * h ^ 26 -
    (137781 : F[X]) * a1 * b7 * h ^ 32 +
    (131220 : F[X]) * a2 ^ 2 * h ^ 36 -
    (218700 : F[X]) * a2 * a3 * a5 * h ^ 30 -
    (78732 : F[X]) * Polynomial.C lambda * a2 * a3 * h ^ 35 -
    (306180 : F[X]) * a2 * a4 ^ 2 * h ^ 30 +
    (102060 : F[X]) * a2 * a4 * a5 ^ 2 * h ^ 24 +
    (183708 : F[X]) * Polynomial.C lambda * a2 * a4 * a5 * h ^ 29 +
    (209952 : F[X]) * a2 * a4 * b8 * h ^ 26 +
    (141750 : F[X]) * a2 * a5 ^ 4 * h ^ 18 -
    (102060 : F[X]) * Polynomial.C lambda * a2 * a5 ^ 3 * h ^ 23 -
    (244944 : F[X]) * a2 * a5 ^ 2 * b8 * h ^ 20 +
    (183708 : F[X]) * a2 * a5 * b7 * h ^ 26 -
    (118098 : F[X]) * a2 * b6 * h ^ 32 -
    (306180 : F[X]) * a3 ^ 2 * a4 * h ^ 30 +
    (51030 : F[X]) * a3 ^ 2 * a5 ^ 2 * h ^ 24 +
    (91854 : F[X]) * Polynomial.C lambda * a3 ^ 2 * a5 * h ^ 29 +
    (104976 : F[X]) * a3 ^ 2 * b8 * h ^ 26 +
    (561330 : F[X]) * a3 * a4 ^ 2 * a5 * h ^ 24 +
    (91854 : F[X]) * Polynomial.C lambda * a3 * a4 ^ 2 * h ^ 29 +
    (56700 : F[X]) * a3 * a4 * a5 ^ 3 * h ^ 18 -
    (306180 : F[X]) * Polynomial.C lambda * a3 * a4 * a5 ^ 2 * h ^ 23 -
    (489888 : F[X]) * a3 * a4 * a5 * b8 * h ^ 20 +
    (183708 : F[X]) * a3 * a4 * b7 * h ^ 26 -
    (159705 : F[X]) * a3 * a5 ^ 5 * h ^ 12 +
    (110565 : F[X]) * Polynomial.C lambda * a3 * a5 ^ 4 * h ^ 17 +
    (272160 : F[X]) * a3 * a5 ^ 3 * b8 * h ^ 14 -
    (214326 : F[X]) * a3 * a5 ^ 2 * b7 * h ^ 20 +
    (157464 : F[X]) * a3 * a5 * b6 * h ^ 26 -
    (98415 : F[X]) * a3 * b5 * h ^ 32 +
    (85050 : F[X]) * a4 ^ 4 * h ^ 24 -
    (226800 : F[X]) * a4 ^ 3 * a5 ^ 2 * h ^ 18 -
    (102060 : F[X]) * Polynomial.C lambda * a4 ^ 3 * a5 * h ^ 23 -
    (81648 : F[X]) * a4 ^ 3 * b8 * h ^ 20 -
    (122850 : F[X]) * a4 ^ 2 * a5 ^ 4 * h ^ 12 +
    (221130 : F[X]) * Polynomial.C lambda * a4 ^ 2 * a5 ^ 3 * h ^ 17 +
    (408240 : F[X]) * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 14 -
    (214326 : F[X]) * a4 ^ 2 * a5 * b7 * h ^ 20 +
    (78732 : F[X]) * a4 ^ 2 * b6 * h ^ 26 +
    (174720 : F[X]) * a4 * a5 ^ 6 * h ^ 6 -
    (117936 : F[X]) * Polynomial.C lambda * a4 * a5 ^ 5 * h ^ 11 -
    (294840 : F[X]) * a4 * a5 ^ 4 * b8 * h ^ 8 +
    (238140 : F[X]) * a4 * a5 ^ 3 * b7 * h ^ 14 -
    (183708 : F[X]) * a4 * a5 ^ 2 * b6 * h ^ 20 +
    (131220 : F[X]) * a4 * a5 * b5 * h ^ 26 -
    (78732 : F[X]) * a4 * b4 * h ^ 32 -
    (34580 : F[X]) * a5 ^ 8 +
    (17784 : F[X]) * Polynomial.C lambda * a5 ^ 7 * h ^ 5 +
    (52416 : F[X]) * a5 ^ 6 * b8 * h ^ 2 -
    (51597 : F[X]) * a5 ^ 5 * b7 * h ^ 8 +
    (51030 : F[X]) * a5 ^ 4 * b6 * h ^ 14 -
    (51030 : F[X]) * a5 ^ 3 * b5 * h ^ 20 +
    (52488 : F[X]) * a5 ^ 2 * b4 * h ^ 26 -
    (59049 : F[X]) * a5 * b3 * h ^ 32 +
    (118098 : F[X]) * b2 * h ^ 38


/-- Exact denominator clearing for the decic `z²` coordinate on the
ninth-power face. -/
theorem depressedV610_eq_cleared
    (h a5 b9 b8 b7 b6 b5 b4 b3 b2 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3
        b2 =
      (-35 * a5 ^ 8 + 8 * lambda * a5 ^ 7 * h ^ 5 +
          112 * a5 ^ 6 * b8 * h ^ 2 - 504 * a5 ^ 5 * b7 * h ^ 8 +
          2160 * a5 ^ 4 * b6 * h ^ 14 - 8640 * a5 ^ 3 * b5 * h ^ 20 +
          31104 * a5 ^ 2 * b4 * h ^ 26 - 93312 * a5 * b3 * h ^ 32 +
          186624 * b2 * h ^ 38) /
        (186624 * h ^ 40) := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h186624 : (186624 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh40 : h ^ 40 ≠ 0 := pow_ne_zero 40 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedV610, sexticDepressionR610, sexticDepressionR68]
  have hrewrite :
      45 * (a5 / (6 * h ^ 5)) ^ 8 -
          36 * (b9 / h ^ 9) * (a5 / (6 * h ^ 5)) ^ 7 +
        28 * (b8 / h ^ 8) * (a5 / (6 * h ^ 5)) ^ 6 -
          21 * (b7 / h ^ 7) * (a5 / (6 * h ^ 5)) ^ 5 +
        15 * (b6 / h ^ 6) * (a5 / (6 * h ^ 5)) ^ 4 -
          10 * (b5 / h ^ 5) * (a5 / (6 * h ^ 5)) ^ 3 +
        6 * (b4 / h ^ 4) * (a5 / (6 * h ^ 5)) ^ 2 -
          3 * (b3 / h ^ 3) * (a5 / (6 * h ^ 5)) + b2 / h ^ 2 =
        (-35 * a5 ^ 8 + 8 * lambda * a5 ^ 7 * h ^ 5 +
            112 * a5 ^ 6 * b8 * h ^ 2 - 504 * a5 ^ 5 * b7 * h ^ 8 +
            2160 * a5 ^ 4 * b6 * h ^ 14 - 8640 * a5 ^ 3 * b5 * h ^ 20 +
            31104 * a5 ^ 2 * b4 * h ^ 26 - 93312 * a5 * b3 * h ^ 32 +
            186624 * b2 * h ^ 38) /
          (186624 * h ^ 40) := by
    field_simp [hh, h6, h3, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh40, h186624]
    have hb9' :
        b9 = (5 * a5 * h ^ 4 - lambda * h ^ 9) / 3 := by
      field_simp [h3]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h6, h3, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh40, h186624]
    ring
  exact hrewrite

/-- Aligned specialization of the weight-forty defect: the fourteen
`λ`-monomials drop. -/
theorem localClearedEighthDefect610_of_lambda_zero
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 : F[X]) :
    localClearedEighthDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3
        b2 0 =
      (262440 : F[X]) * a0 * a4 * h ^ 36 +
        (87480 : F[X]) * a0 * a5 ^ 2 * h ^ 30 -
        (157464 : F[X]) * a0 * b8 * h ^ 32 +
        (262440 : F[X]) * a1 * a3 * h ^ 36 -
        (218700 : F[X]) * a1 * a4 * a5 * h ^ 30 -
        (119070 : F[X]) * a1 * a5 ^ 3 * h ^ 24 +
        (209952 : F[X]) * a1 * a5 * b8 * h ^ 26 -
        (137781 : F[X]) * a1 * b7 * h ^ 32 +
        (131220 : F[X]) * a2 ^ 2 * h ^ 36 -
        (218700 : F[X]) * a2 * a3 * a5 * h ^ 30 -
        (306180 : F[X]) * a2 * a4 ^ 2 * h ^ 30 +
        (102060 : F[X]) * a2 * a4 * a5 ^ 2 * h ^ 24 +
        (209952 : F[X]) * a2 * a4 * b8 * h ^ 26 +
        (141750 : F[X]) * a2 * a5 ^ 4 * h ^ 18 -
        (244944 : F[X]) * a2 * a5 ^ 2 * b8 * h ^ 20 +
        (183708 : F[X]) * a2 * a5 * b7 * h ^ 26 -
        (118098 : F[X]) * a2 * b6 * h ^ 32 -
        (306180 : F[X]) * a3 ^ 2 * a4 * h ^ 30 +
        (51030 : F[X]) * a3 ^ 2 * a5 ^ 2 * h ^ 24 +
        (104976 : F[X]) * a3 ^ 2 * b8 * h ^ 26 +
        (561330 : F[X]) * a3 * a4 ^ 2 * a5 * h ^ 24 +
        (56700 : F[X]) * a3 * a4 * a5 ^ 3 * h ^ 18 -
        (489888 : F[X]) * a3 * a4 * a5 * b8 * h ^ 20 +
        (183708 : F[X]) * a3 * a4 * b7 * h ^ 26 -
        (159705 : F[X]) * a3 * a5 ^ 5 * h ^ 12 +
        (272160 : F[X]) * a3 * a5 ^ 3 * b8 * h ^ 14 -
        (214326 : F[X]) * a3 * a5 ^ 2 * b7 * h ^ 20 +
        (157464 : F[X]) * a3 * a5 * b6 * h ^ 26 -
        (98415 : F[X]) * a3 * b5 * h ^ 32 +
        (85050 : F[X]) * a4 ^ 4 * h ^ 24 -
        (226800 : F[X]) * a4 ^ 3 * a5 ^ 2 * h ^ 18 -
        (81648 : F[X]) * a4 ^ 3 * b8 * h ^ 20 -
        (122850 : F[X]) * a4 ^ 2 * a5 ^ 4 * h ^ 12 +
        (408240 : F[X]) * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 14 -
        (214326 : F[X]) * a4 ^ 2 * a5 * b7 * h ^ 20 +
        (78732 : F[X]) * a4 ^ 2 * b6 * h ^ 26 +
        (174720 : F[X]) * a4 * a5 ^ 6 * h ^ 6 -
        (294840 : F[X]) * a4 * a5 ^ 4 * b8 * h ^ 8 +
        (238140 : F[X]) * a4 * a5 ^ 3 * b7 * h ^ 14 -
        (183708 : F[X]) * a4 * a5 ^ 2 * b6 * h ^ 20 +
        (131220 : F[X]) * a4 * a5 * b5 * h ^ 26 -
        (78732 : F[X]) * a4 * b4 * h ^ 32 -
        (34580 : F[X]) * a5 ^ 8 +
        (52416 : F[X]) * a5 ^ 6 * b8 * h ^ 2 -
        (51597 : F[X]) * a5 ^ 5 * b7 * h ^ 8 +
        (51030 : F[X]) * a5 ^ 4 * b6 * h ^ 14 -
        (51030 : F[X]) * a5 ^ 3 * b5 * h ^ 20 +
        (52488 : F[X]) * a5 ^ 2 * b4 * h ^ 26 -
        (59049 : F[X]) * a5 * b3 * h ^ 32 +
        (118098 : F[X]) * b2 * h ^ 38 := by
  simp [localClearedEighthDefect610, map_zero]

set_option maxHeartbeats 32000000 in
/-- Clearing the first integral
`V - (4/3) α E - (7/6) β D - γ C - (5/6) δ B - (2/3) ε A
- (10/9) A E - (10/9) B D - (5/9) C² + (5/27) A B² + (5/27) A² C
- (5/243) A⁴ + (4/81) α A³ - (4/9) α A C - (2/9) α B² - (7/36) β A B
- (3/4) L A D - (3/4) L B C + (3/16) L A² B`
against `h⁴⁰` on the ninth-power face. -/
theorem eighthDefect_eq_clearedEta610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (118098 : F) * h ^ 40 *
        etaResidual610
          (depressedL610 h (sexticDepressionR610 h a5) b9)
          (depressedA610 h (sexticDepressionR610 h a5) a5 a4)
          (depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3)
          (depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2)
          (depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1)
          (depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1
            a0)
          (depressedP610 h (sexticDepressionR610 h a5) b9 b8)
          (depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7)
          (depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6)
          (depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5)
          (depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4)
          (depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3 b2) =
  (262440 : F) * a0 * a4 * h ^ 36 +
    (87480 : F) * a0 * a5 ^ 2 * h ^ 30 -
    (78732 : F) * lambda * a0 * a5 * h ^ 35 -
    (157464 : F) * a0 * b8 * h ^ 32 +
    (262440 : F) * a1 * a3 * h ^ 36 -
    (218700 : F) * a1 * a4 * a5 * h ^ 30 -
    (78732 : F) * lambda * a1 * a4 * h ^ 35 -
    (119070 : F) * a1 * a5 ^ 3 * h ^ 24 +
    (91854 : F) * lambda * a1 * a5 ^ 2 * h ^ 29 +
    (209952 : F) * a1 * a5 * b8 * h ^ 26 -
    (137781 : F) * a1 * b7 * h ^ 32 +
    (131220 : F) * a2 ^ 2 * h ^ 36 -
    (218700 : F) * a2 * a3 * a5 * h ^ 30 -
    (78732 : F) * lambda * a2 * a3 * h ^ 35 -
    (306180 : F) * a2 * a4 ^ 2 * h ^ 30 +
    (102060 : F) * a2 * a4 * a5 ^ 2 * h ^ 24 +
    (183708 : F) * lambda * a2 * a4 * a5 * h ^ 29 +
    (209952 : F) * a2 * a4 * b8 * h ^ 26 +
    (141750 : F) * a2 * a5 ^ 4 * h ^ 18 -
    (102060 : F) * lambda * a2 * a5 ^ 3 * h ^ 23 -
    (244944 : F) * a2 * a5 ^ 2 * b8 * h ^ 20 +
    (183708 : F) * a2 * a5 * b7 * h ^ 26 -
    (118098 : F) * a2 * b6 * h ^ 32 -
    (306180 : F) * a3 ^ 2 * a4 * h ^ 30 +
    (51030 : F) * a3 ^ 2 * a5 ^ 2 * h ^ 24 +
    (91854 : F) * lambda * a3 ^ 2 * a5 * h ^ 29 +
    (104976 : F) * a3 ^ 2 * b8 * h ^ 26 +
    (561330 : F) * a3 * a4 ^ 2 * a5 * h ^ 24 +
    (91854 : F) * lambda * a3 * a4 ^ 2 * h ^ 29 +
    (56700 : F) * a3 * a4 * a5 ^ 3 * h ^ 18 -
    (306180 : F) * lambda * a3 * a4 * a5 ^ 2 * h ^ 23 -
    (489888 : F) * a3 * a4 * a5 * b8 * h ^ 20 +
    (183708 : F) * a3 * a4 * b7 * h ^ 26 -
    (159705 : F) * a3 * a5 ^ 5 * h ^ 12 +
    (110565 : F) * lambda * a3 * a5 ^ 4 * h ^ 17 +
    (272160 : F) * a3 * a5 ^ 3 * b8 * h ^ 14 -
    (214326 : F) * a3 * a5 ^ 2 * b7 * h ^ 20 +
    (157464 : F) * a3 * a5 * b6 * h ^ 26 -
    (98415 : F) * a3 * b5 * h ^ 32 +
    (85050 : F) * a4 ^ 4 * h ^ 24 -
    (226800 : F) * a4 ^ 3 * a5 ^ 2 * h ^ 18 -
    (102060 : F) * lambda * a4 ^ 3 * a5 * h ^ 23 -
    (81648 : F) * a4 ^ 3 * b8 * h ^ 20 -
    (122850 : F) * a4 ^ 2 * a5 ^ 4 * h ^ 12 +
    (221130 : F) * lambda * a4 ^ 2 * a5 ^ 3 * h ^ 17 +
    (408240 : F) * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 14 -
    (214326 : F) * a4 ^ 2 * a5 * b7 * h ^ 20 +
    (78732 : F) * a4 ^ 2 * b6 * h ^ 26 +
    (174720 : F) * a4 * a5 ^ 6 * h ^ 6 -
    (117936 : F) * lambda * a4 * a5 ^ 5 * h ^ 11 -
    (294840 : F) * a4 * a5 ^ 4 * b8 * h ^ 8 +
    (238140 : F) * a4 * a5 ^ 3 * b7 * h ^ 14 -
    (183708 : F) * a4 * a5 ^ 2 * b6 * h ^ 20 +
    (131220 : F) * a4 * a5 * b5 * h ^ 26 -
    (78732 : F) * a4 * b4 * h ^ 32 -
    (34580 : F) * a5 ^ 8 +
    (17784 : F) * lambda * a5 ^ 7 * h ^ 5 +
    (52416 : F) * a5 ^ 6 * b8 * h ^ 2 -
    (51597 : F) * a5 ^ 5 * b7 * h ^ 8 +
    (51030 : F) * a5 ^ 4 * b6 * h ^ 14 -
    (51030 : F) * a5 ^ 3 * b5 * h ^ 20 +
    (52488 : F) * a5 ^ 2 * b4 * h ^ 26 -
    (59049 : F) * a5 * b3 * h ^ 32 +
    (118098 : F) * b2 * h ^ 38 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h4 : (4 : F) ≠ 0 := by norm_num
  have h5 : (5 : F) ≠ 0 := by norm_num
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h8 : (8 : F) ≠ 0 := by norm_num
  have h9 : (9 : F) ≠ 0 := by norm_num
  have h12 : (12 : F) ≠ 0 := by norm_num
  have h16 : (16 : F) ≠ 0 := by norm_num
  have h18 : (18 : F) ≠ 0 := by norm_num
  have h27 : (27 : F) ≠ 0 := by norm_num
  have h36 : (36 : F) ≠ 0 := by norm_num
  have h54 : (54 : F) ≠ 0 := by norm_num
  have h72 : (72 : F) ≠ 0 := by norm_num
  have h81 : (81 : F) ≠ 0 := by norm_num
  have h144 : (144 : F) ≠ 0 := by norm_num
  have h216 : (216 : F) ≠ 0 := by norm_num
  have h243 : (243 : F) ≠ 0 := by norm_num
  have h324 : (324 : F) ≠ 0 := by norm_num
  have h432 : (432 : F) ≠ 0 := by norm_num
  have h648 : (648 : F) ≠ 0 := by norm_num
  have h7776 : (7776 : F) ≠ 0 := by norm_num
  have h11664 : (11664 : F) ≠ 0 := by norm_num
  have h46656 : (46656 : F) ≠ 0 := by norm_num
  have h93312 : (93312 : F) ≠ 0 := by norm_num
  have h118098 : (118098 : F) ≠ 0 := by norm_num
  have h186624 : (186624 : F) ≠ 0 := by norm_num
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hh25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
  have hh30 : h ^ 30 ≠ 0 := pow_ne_zero 30 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh40 : h ^ 40 ≠ 0 := pow_ne_zero 40 hh
  have hL :
      depressedL610 h (sexticDepressionR610 h a5) b9 = -lambda / 3 :=
    depressedL610_eq_of_ninthPower h a5 b9 lambda hh hN
  have hA :
      depressedA610 h (sexticDepressionR610 h a5) a5 a4 =
        (12 * a4 * h ^ 6 - 5 * a5 ^ 2) / (12 * h ^ 10) :=
    depressedA610_eq_cleared h a5 a4 hh
  have hB :
      depressedB610 h (sexticDepressionR610 h a5) a5 a4 a3 =
        (54 * a3 * h ^ 12 - 36 * a4 * a5 * h ^ 6 + 10 * a5 ^ 3) /
          (54 * h ^ 15) :=
    depressedB610_eq_cleared h a5 a4 a3 hh
  have hC :
      depressedC610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 =
        (144 * a2 * h ^ 18 - 72 * a3 * a5 * h ^ 12 +
            24 * a4 * a5 ^ 2 * h ^ 6 - 5 * a5 ^ 4) /
          (144 * h ^ 20) :=
    depressedC610_eq_cleared h a5 a4 a3 a2 hh
  have hD0 :
      depressedD610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 =
        (324 * a1 * h ^ 24 - 108 * a2 * a5 * h ^ 18 +
            27 * a3 * a5 ^ 2 * h ^ 12 - 6 * a4 * a5 ^ 3 * h ^ 6 +
            a5 ^ 5) /
          (324 * h ^ 25) :=
    depressedD610_eq_cleared h a5 a4 a3 a2 a1 hh
  have hE0 :
      depressedE610 h (sexticDepressionR610 h a5) a5 a4 a3 a2 a1 a0 =
        (46656 * a0 * h ^ 30 - 7776 * a1 * a5 * h ^ 24 +
            1296 * a2 * a5 ^ 2 * h ^ 18 - 216 * a3 * a5 ^ 3 * h ^ 12 +
            36 * a4 * a5 ^ 4 * h ^ 6 - 5 * a5 ^ 6) /
          (46656 * h ^ 30) :=
    depressedE610_eq_cleared h a5 a4 a3 a2 a1 a0 hh
  have hS :
      depressedS610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 =
        (28 * a5 ^ 5 - 7 * lambda * a5 ^ 4 * h ^ 5 -
            56 * a5 ^ 3 * b8 * h ^ 2 + 126 * a5 ^ 2 * b7 * h ^ 8 -
            216 * a5 * b6 * h ^ 14 + 216 * b5 * h ^ 20) /
          (216 * h ^ 25) :=
    depressedS610_eq_cleared h a5 b9 b8 b7 b6 b5 lambda hh hN
  have hT :
      depressedT610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 =
        (-175 * a5 ^ 6 + 42 * lambda * a5 ^ 5 * h ^ 5 +
            420 * a5 ^ 4 * b8 * h ^ 2 - 1260 * a5 ^ 3 * b7 * h ^ 8 +
            3240 * a5 ^ 2 * b6 * h ^ 14 - 6480 * a5 * b5 * h ^ 20 +
            7776 * b4 * h ^ 26) /
          (7776 * h ^ 30) :=
    depressedT610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 lambda hh hN
  have hV :
      depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 b2 =
        (-35 * a5 ^ 8 + 8 * lambda * a5 ^ 7 * h ^ 5 +
            112 * a5 ^ 6 * b8 * h ^ 2 - 504 * a5 ^ 5 * b7 * h ^ 8 +
            2160 * a5 ^ 4 * b6 * h ^ 14 - 8640 * a5 ^ 3 * b5 * h ^ 20 +
            31104 * a5 ^ 2 * b4 * h ^ 26 - 93312 * a5 * b3 * h ^ 32 +
            186624 * b2 * h ^ 38) /
          (186624 * h ^ 40) :=
    depressedV610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 lambda hh hN
  have hP :
      depressedP610 h (sexticDepressionR610 h a5) b9 b8 =
        (-5 * a5 ^ 2 + 2 * lambda * a5 * h ^ 5 + 4 * b8 * h ^ 2) /
          (4 * h ^ 10) :=
    depressedP610_eq_cleared_ninthPower h a5 b9 b8 lambda hh hN
  have hQ :
      depressedQ610 h (sexticDepressionR610 h a5) b9 b8 b7 =
        (10 * a5 ^ 3 - 3 * lambda * a5 ^ 2 * h ^ 5 -
            12 * a5 * b8 * h ^ 2 + 9 * b7 * h ^ 8) /
          (9 * h ^ 15) :=
    depressedQ610_eq_cleared h a5 b9 b8 b7 lambda hh hN
  have hR :
      depressedR610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 =
        (-210 * a5 ^ 4 + 56 * lambda * a5 ^ 3 * h ^ 5 +
            336 * a5 ^ 2 * b8 * h ^ 2 - 504 * a5 * b7 * h ^ 8 +
            432 * b6 * h ^ 14) /
          (432 * h ^ 20) :=
    depressedR610_eq_cleared h a5 b9 b8 b7 b6 lambda hh hN
  simp only [etaResidual610, hL, hA, hB, hC, hD0, hE0, hP, hQ, hR, hS,
    hT, hV, alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610]
  field_simp [hh, h2, h3, h4, h5, h6, h8, h9, h12, h16, h18, h27, h36,
    h54, h72, h81, h144, h216, h243, h324, h432, h648, h7776, h11664,
    h46656, h93312, h118098, h186624, hh10, hh15, hh20, hh25, hh30,
    hh35, hh40]
  ring

end Depression610Eighth

/-! ## Degree-`7` depressed Jacobian coefficient -/

section DepressedRow610Eighth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`7` Jacobian coefficient is
exactly `8 P E' + 7 Q D' + 6 R C' + 5 S B' + 4 T A' - D Q' - 2 C R'
- 3 B S' - 4 A T' - 6 V'`. -/
theorem differentialJacobian_coeff_7_monicSexticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 7 =
      (8 : F) * g.coeff 8 * d (f.coeff 0) +
        (7 : F) * g.coeff 7 * d (f.coeff 1) +
        (6 : F) * g.coeff 6 * d (f.coeff 2) +
        (5 : F) * g.coeff 5 * d (f.coeff 3) +
        (4 : F) * g.coeff 4 * d (f.coeff 4) -
          (1 : F) * f.coeff 1 * d (g.coeff 7) -
          (2 : F) * f.coeff 2 * d (g.coeff 6) -
          (3 : F) * f.coeff 3 * d (g.coeff 5) -
          (4 : F) * f.coeff 4 * d (g.coeff 4) -
          (6 : F) * d (g.coeff 2) := by
  have hfd_high : ∀ n, 5 ≤ n → (coefficientDeriv d f).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      simpa [hf5]
    · have : 6 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq6 | hlt6
      · subst n
        simpa [hf6, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hf_high n (by omega))
  have hgd_high : ∀ n, 10 ≤ n → g.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 10 < n + 1 := by omega
    simp [hg_high (n + 1) this]
  have hfd'_high : ∀ n, 6 ≤ n → f.derivative.coeff n = 0 := by
    intro n hn
    rw [Polynomial.coeff_derivative]
    have : 6 < n + 1 := by omega
    simp [hf_high (n + 1) this]
  have hgd'_high : ∀ n, 9 ≤ n → (coefficientDeriv d g).coeff n = 0 := by
    intro n hn
    rw [coeff_coefficientDeriv]
    rcases Nat.eq_or_lt_of_le hn with hEq | hlt
    · subst n
      exact hL
    · have : 10 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with hEq10 | hlt10
      · subst n
        simpa [hg10, d.map_one_eq_zero]
      · exact d.map_zero ▸ congrArg d (hg_high n (by omega))
  have hmem08 : ((0, 7) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem17 : ((1, 6) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem26 : ((2, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem35 : ((3, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem44 : ((4, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem53 : ((5, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 7 =
        (8 : F) * g.coeff 8 * d (f.coeff 0) +
          (7 : F) * g.coeff 7 * d (f.coeff 1) +
          (6 : F) * g.coeff 6 * d (f.coeff 2) +
          (5 : F) * g.coeff 5 * d (f.coeff 3) +
          (4 : F) * g.coeff 4 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 7) : ℕ × ℕ) ≠ (1, 6) := by decide
    have hne08_26 : ((0, 7) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne08_35 : ((0, 7) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne08_44 : ((0, 7) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne17_26 : ((1, 6) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne17_35 : ((1, 6) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne17_44 : ((1, 6) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne26_35 : ((2, 5) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne26_44 : ((2, 5) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hne35_44 : ((3, 4) : ℕ × ℕ) ≠ (4, 3) := by decide
    have hsubset :
        ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3)} : Finset (ℕ × ℕ)) ⊆
          Finset.HasAntidiagonal.antidiagonal (7 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem08
      · subst b; exact hmem17
      · subst b; exact hmem26
      · subst b; exact hmem35
      · subst b; exact hmem44
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 7 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 7) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne44 : b ≠ (4, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 5 ≤ b.1
      · simp [hfd_high b.1 hige]
      · have hne0 : b.1 ≠ 0 := by
          intro h0
          apply hne08
          ext
          · exact h0
          · omega
        have hne1 : b.1 ≠ 1 := by
          intro h1
          apply hne17
          ext
          · exact h1
          · omega
        have hne2 : b.1 ≠ 2 := by
          intro h2
          apply hne26
          ext
          · exact h2
          · omega
        have hne3 : b.1 ≠ 3 := by
          intro h3
          apply hne35
          ext
          · exact h3
          · omega
        have hne4 : b.1 ≠ 4 := by
          intro h4
          apply hne44
          ext
          · exact h4
          · omega
        omega
    have hpair :
        (∑ p ∈ ({(0, 7), (1, 6), (2, 5), (3, 4), (4, 3)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 7 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 6 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 3 := by
      rw [Finset.sum_insert (by simp [hne08_17, hne08_26, hne08_35, hne08_44]),
        Finset.sum_insert (by simp [hne17_26, hne17_35, hne17_44]),
        Finset.sum_insert (by simp [hne26_35, hne26_44]),
        Finset.sum_insert (by simp [hne35_44]), Finset.sum_singleton]
      ring
    have hder7 : g.derivative.coeff 7 = (8 : F) * g.coeff 8 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder6 : g.derivative.coeff 6 = (7 : F) * g.coeff 7 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : g.derivative.coeff 5 = (6 : F) * g.coeff 6 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder4 : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3 : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder7, hder6, hder5, hder4, hder3]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 7 =
        (1 : F) * f.coeff 1 * d (g.coeff 7) +
          (2 : F) * f.coeff 2 * d (g.coeff 6) +
          (3 : F) * f.coeff 3 * d (g.coeff 5) +
          (4 : F) * f.coeff 4 * d (g.coeff 4) +
          (6 : F) * d (g.coeff 2) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 7) : ℕ × ℕ) ≠ (1, 6) := by decide
    have hne08_26 : ((0, 7) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne08_35 : ((0, 7) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne08_53 : ((0, 7) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne17_26 : ((1, 6) : ℕ × ℕ) ≠ (2, 5) := by decide
    have hne17_35 : ((1, 6) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne17_53 : ((1, 6) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne26_35 : ((2, 5) : ℕ × ℕ) ≠ (3, 4) := by decide
    have hne26_53 : ((2, 5) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hne35_53 : ((3, 4) : ℕ × ℕ) ≠ (5, 2) := by decide
    have hsubset : ({(0, 7), (1, 6), (2, 5), (3, 4), (5, 2)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (7 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem08
      · subst b; exact hmem17
      · subst b; exact hmem26
      · subst b; exact hmem35
      · subst b; exact hmem53
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (7 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 7), (1, 6), (2, 5), (3, 4), (5, 2)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 7 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 7) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 6) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 5) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne53 : b ≠ (5, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      by_cases hige : 6 ≤ b.1
      · simp [hfd'_high b.1 hige]
      · by_cases h4 : b.1 = 4
        · have hf4 : f.derivative.coeff b.1 = 0 := by
            rw [h4, Polynomial.coeff_derivative, hf5]
            simp
          simp [hf4]
        · have hne0 : b.1 ≠ 0 := by
            intro h0
            apply hne08
            ext
            · exact h0
            · omega
          have hne1 : b.1 ≠ 1 := by
            intro h1
            apply hne17
            ext
            · exact h1
            · omega
          have hne2 : b.1 ≠ 2 := by
            intro h2
            apply hne26
            ext
            · exact h2
            · omega
          have hne3 : b.1 ≠ 3 := by
            intro h3
            apply hne35
            ext
            · exact h3
            · omega
          have hne5 : b.1 ≠ 5 := by
            intro h5
            apply hne53
            ext
            · exact h5
            · omega
          omega
    have hpair :
        (∑ p ∈ ({(0, 7), (1, 6), (2, 5), (3, 4), (5, 2)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 7 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 6 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 2 := by
      rw [Finset.sum_insert (by simp [hne08_17, hne08_26, hne08_35, hne08_53]),
        Finset.sum_insert (by simp [hne17_26, hne17_35, hne17_53]),
        Finset.sum_insert (by simp [hne26_35, hne26_53]),
        Finset.sum_insert (by simp [hne35_53]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = (1 : F) * f.coeff 1 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3 : f.derivative.coeff 3 = (4 : F) * f.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder5 : f.derivative.coeff 5 = (6 : F) := by
      rw [Polynomial.coeff_derivative, hf6]
      norm_num
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder2, hder3, hder5]
    try ring
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring

set_option maxHeartbeats 8000000 in
theorem etaResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R S0 T0 V0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hgamma : d (gammaResidual610 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual610 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual610 L A B C0 D0 E0 P Q R T0) = 0)
    (hrow : (8 : F) * P * d E0 + (7 : F) * Q * d D0 +
        (6 : F) * R * d C0 + (5 : F) * S0 * d B +
        (4 : F) * T0 * d A - (1 : F) * D0 * d Q -
        (2 : F) * C0 * d R - (3 : F) * B * d S0 -
        (4 : F) * A * d T0 - (6 : F) * d V0 = 0) :
    d (etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h6 : d (6 : F) = 0 := d.map_natCast 6
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h10 : d (10 : F) = 0 := d.map_natCast 10
  have h14 : d (14 : F) = 0 := d.map_natCast 14
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h18 : d (18 : F) = 0 := d.map_natCast 18
  have h20 : d (20 : F) = 0 := d.map_natCast 20
  have h25 : d (25 : F) = 0 := d.map_natCast 25
  have h27 : d (27 : F) = 0 := d.map_natCast 27
  have h56 : d (56 : F) = 0 := d.map_natCast 56
  have h70 : d (70 : F) = 0 := d.map_natCast 70
  have h81 : d (81 : F) = 0 := d.map_natCast 81
  have h100 : d (100 : F) = 0 := d.map_natCast 100
  have h175 : d (175 : F) = 0 := d.map_natCast 175
  have h243 : d (243 : F) = 0 := d.map_natCast 243
  have h53 : d (5 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h5]
  have h32 : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  have h43 : d (4 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h4]
  have h76 : d (7 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h7]
  have hP0 : d P - (5 / 3 : F) * d A = 0 := by
    simpa [alphaResidual610, map_sub, Derivation.leibniz, h53, zero_mul,
      add_zero] using halpha
  have hQ0 : d Q - (5 / 3 : F) * d B - (3 / 2 : F) * L * d A = 0 := by
    simpa [betaResidual610, map_sub, Derivation.leibniz, h53, h32, hL,
      zero_mul, add_zero, mul_zero] using hbeta
  have hG0 :
      d R - (5 / 3 : F) * d C0 - (3 / 2 : F) * L * d B -
        (4 / 3 : F) * A * d P - (4 / 3 : F) * P * d A +
        (10 / 3 : F) * A * d A = 0 := by
    have hgamma' :
        d R - (5 / 3 : F) * d C0 - (3 / 2 : F) * L * d B -
          ((4 / 3 : F) * P * d A + A * ((4 / 3 : F) * d P)) +
          (5 / 3 : F) * (A * d A + A * d A) = 0 := by
      simpa [gammaResidual610, map_sub, map_add, Derivation.leibniz, h53,
        h32, h43, hL, zero_mul, add_zero, mul_zero, pow_two] using hgamma
    linear_combination hgamma'
  have hDlt0 :
      d S0 - (5 / 3 : F) * d D0 - (3 / 2 : F) * L * d C0 -
        (4 / 3 : F) * P * d B - (4 / 3 : F) * B * d P -
        (7 / 6 : F) * Q * d A - (7 / 6 : F) * A * d Q +
        (55 / 18 : F) * A * d B + (55 / 18 : F) * B * d A +
        (11 / 4 : F) * L * A * d A = 0 := by
    have hsqA : d (A * A) = (2 : F) * A * d A := by
      simp [Derivation.leibniz]
      ring
    have h5518 : d (55 / 18 : F) = 0 := by
      have h55 : d (55 : F) = 0 := d.map_natCast 55
      simp [Derivation.leibniz_div, h18, h55]
    have h118 : d (11 / 8 : F) = 0 := by
      have h11 : d (11 : F) = 0 := d.map_natCast 11
      simp [Derivation.leibniz_div, h8, h11]
    have hexp :
        deltaResidual610 L A B C0 D0 P Q S0 =
          S0 - (5 / 3 : F) * D0 - (3 / 2 : F) * L * C0 -
            (4 / 3 : F) * P * B - (7 / 6 : F) * Q * A +
            (55 / 18 : F) * A * B + (11 / 8 : F) * L * (A * A) := by
      simp only [deltaResidual610, alphaResidual610, betaResidual610,
        pow_two]
      ring
    have hdlt := hdelta
    rw [hexp] at hdlt
    simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
      h5518, h118, zero_mul, add_zero, mul_zero, hsqA] at hdlt
    linear_combination hdlt
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hcub : d (A * A * A) = (3 : F) * (A * A) * d A := by
    simp [Derivation.leibniz]
    ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have h259 : d (25 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h25]
  have h2518 : d (25 / 18 : F) = 0 := by
    simp [Derivation.leibniz_div, h18, h25]
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h5]
  have h109 : d (10 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h10]
  have h10081 : d (100 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h100]
  have hEps0 :
      d T0 - (5 / 3 : F) * d E0 - (3 / 2 : F) * L * d D0 -
        (4 / 3 : F) * P * d C0 - (4 / 3 : F) * C0 * d P -
        (7 / 6 : F) * Q * d B - (7 / 6 : F) * B * d Q -
        R * d A - A * d R + (25 / 9 : F) * A * d C0 +
        (25 / 9 : F) * C0 * d A + (25 / 9 : F) * B * d B +
        (5 / 2 : F) * L * A * d B + (5 / 2 : F) * L * B * d A +
        (20 / 9 : F) * P * A * d A + (10 / 9 : F) * (A * A) * d P -
        (100 / 27 : F) * (A * A) * d A = 0 := by
    have hexp :
        epsilonResidual610 L A B C0 D0 E0 P Q R T0 =
          T0 - (5 / 3 : F) * E0 - (3 / 2 : F) * L * D0 -
            (4 / 3 : F) * P * C0 - (7 / 6 : F) * Q * B - R * A +
            (25 / 9 : F) * A * C0 + (25 / 18 : F) * (B * B) +
            (5 / 2 : F) * L * A * B + (10 / 9 : F) * P * (A * A) -
            (100 / 81 : F) * (A * A * A) := by
      simp only [epsilonResidual610, alphaResidual610, betaResidual610,
        gammaResidual610, pow_two, pow_three]
      ring
    have heps := hepsilon
    rw [hexp] at heps
    simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
      h259, h2518, h52, h109, h10081, zero_mul, add_zero, mul_zero, hsq,
      hcub, hsqB] at heps
    linear_combination heps
  have heta :
      etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 =
        V0 - (2 / 3 : F) * A * T0 - (5 / 6 : F) * B * S0 - C0 * R +
          (2 / 3 : F) * (A * A) * R - (7 / 6 : F) * D0 * Q +
          (14 / 9 : F) * A * B * Q - (4 / 3 : F) * E0 * P +
          (16 / 9 : F) * A * C0 * P + (8 / 9 : F) * (B * B) * P -
          (56 / 81 : F) * (A * A * A) * P + (20 / 9 : F) * A * E0 +
          (20 / 9 : F) * B * D0 + (10 / 9 : F) * (C0 * C0) +
          (2 : F) * A * D0 * L + (2 : F) * B * C0 * L -
          (7 / 3 : F) * (A * A) * B * L - (70 / 27 : F) * (A * A) * C0 -
          (70 / 27 : F) * A * (B * B) +
          (175 / 243 : F) * (A * A * A * A) := by
    simp only [etaResidual610, alphaResidual610, betaResidual610,
      gammaResidual610, deltaResidual610, epsilonResidual610, pow_two,
      pow_three]
    ring
  have h23 : d (2 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h2]
  have h56c : d (5 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h5]
  have h149 : d (14 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h14]
  have h169 : d (16 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h16]
  have h89 : d (8 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h8]
  have h5681 : d (56 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h56]
  have h209 : d (20 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h20]
  have h73 : d (7 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h7]
  have h7027 : d (70 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h70]
  have h175243 : d (175 / 243 : F) = 0 := by
    simp [Derivation.leibniz_div, h243, h175]
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hquart : d (A * A * A * A) =
      (4 : F) * (A * A * A) * d A := by
    simp [Derivation.leibniz]
    ring
  have hdAT : d ((2 / 3 : F) * A * T0) =
      (2 / 3 : F) * (d A * T0 + A * d T0) := by
    simp [Derivation.leibniz, smul_eq_mul, h23]
    ring
  have hdBS : d ((5 / 6 : F) * B * S0) =
      (5 / 6 : F) * (d B * S0 + B * d S0) := by
    simp [Derivation.leibniz, smul_eq_mul, h56c]
    ring
  have hdCR : d (C0 * R) = d C0 * R + C0 * d R := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hdA2R : d ((2 / 3 : F) * (A * A) * R) =
      (2 / 3 : F) * ((2 : F) * A * d A * R + (A * A) * d R) := by
    simp [Derivation.leibniz, smul_eq_mul, h23, hsq]
    ring
  have hdDQ : d ((7 / 6 : F) * D0 * Q) =
      (7 / 6 : F) * (d D0 * Q + D0 * d Q) := by
    simp [Derivation.leibniz, smul_eq_mul, h76]
    ring
  have hdABQ : d ((14 / 9 : F) * A * B * Q) =
      (14 / 9 : F) * (d A * B * Q + A * d B * Q + A * B * d Q) := by
    simp [Derivation.leibniz, smul_eq_mul, h149]
    ring
  have hdEP : d ((4 / 3 : F) * E0 * P) =
      (4 / 3 : F) * (d E0 * P + E0 * d P) := by
    simp [Derivation.leibniz, smul_eq_mul, h43]
    ring
  have hdACP : d ((16 / 9 : F) * A * C0 * P) =
      (16 / 9 : F) * (d A * C0 * P + A * d C0 * P + A * C0 * d P) := by
    simp [Derivation.leibniz, smul_eq_mul, h169]
    ring
  have hdB2P : d ((8 / 9 : F) * (B * B) * P) =
      (8 / 9 : F) * ((2 : F) * B * d B * P + (B * B) * d P) := by
    simp [Derivation.leibniz, smul_eq_mul, h89, hsqB]
    ring
  have hdA3P : d ((56 / 81 : F) * (A * A * A) * P) =
      (56 / 81 : F) * ((3 : F) * (A * A) * d A * P +
        (A * A * A) * d P) := by
    simp [Derivation.leibniz, smul_eq_mul, h5681, hcub]
    ring
  have hdAE : d ((20 / 9 : F) * A * E0) =
      (20 / 9 : F) * (d A * E0 + A * d E0) := by
    simp [Derivation.leibniz, smul_eq_mul, h209]
    ring
  have hdBD : d ((20 / 9 : F) * B * D0) =
      (20 / 9 : F) * (d B * D0 + B * d D0) := by
    simp [Derivation.leibniz, smul_eq_mul, h209]
    ring
  have hdC2 : d ((10 / 9 : F) * (C0 * C0)) =
      (10 / 9 : F) * ((2 : F) * C0 * d C0) := by
    simp [Derivation.leibniz, smul_eq_mul, h109, hsqC]
    try ring
  have hdADL : d ((2 : F) * A * D0 * L) =
      (2 : F) * L * (d A * D0 + A * d D0) := by
    simp [Derivation.leibniz, smul_eq_mul, h2, hL, zero_mul, add_zero]
    ring
  have hdBCL : d ((2 : F) * B * C0 * L) =
      (2 : F) * L * (d B * C0 + B * d C0) := by
    simp [Derivation.leibniz, smul_eq_mul, h2, hL, zero_mul, add_zero]
    ring
  have hdA2BL : d ((7 / 3 : F) * (A * A) * B * L) =
      (7 / 3 : F) * L * ((2 : F) * A * d A * B + (A * A) * d B) := by
    simp [Derivation.leibniz, smul_eq_mul, h73, hL, hsq, zero_mul,
      add_zero]
    ring
  have hdA2C : d ((70 / 27 : F) * (A * A) * C0) =
      (70 / 27 : F) * ((2 : F) * A * d A * C0 + (A * A) * d C0) := by
    simp [Derivation.leibniz, smul_eq_mul, h7027, hsq]
    ring
  have hdAB2 : d ((70 / 27 : F) * A * (B * B)) =
      (70 / 27 : F) * (d A * (B * B) + A * ((2 : F) * B * d B)) := by
    simp [Derivation.leibniz, smul_eq_mul, h7027, hsqB]
    ring
  have hdA4 : d ((175 / 243 : F) * (A * A * A * A)) =
      (175 / 243 : F) * ((4 : F) * (A * A * A) * d A) := by
    simp [Derivation.leibniz, smul_eq_mul, h175243, hquart]
    try ring
  rw [heta]
  simp only [map_sub, map_add, hdAT, hdBS, hdCR, hdA2R, hdDQ, hdABQ,
    hdEP, hdACP, hdB2P, hdA3P, hdAE, hdBD, hdC2, hdADL, hdBCL, hdA2BL,
    hdA2C, hdAB2, hdA4]
  linear_combination (-1 / 6 : F) * hrow +
    (-(4 / 3 : F) * A) * hEps0 +
    (-(4 / 3 : F) * B) * hDlt0 +
    (-(2 / 3 : F) * (A * A) - (4 / 3 : F) * C0) * hG0 +
    (-(14 / 9 : F) * A * B - (4 / 3 : F) * D0) * hQ0 +
    (-(8 / 81 : F) * (A * A * A) - (16 / 9 : F) * A * C0 -
        (8 / 9 : F) * (B * B) - (4 / 3 : F) * E0) * hP0

end DepressedRow610Eighth

/-! ## Affine depression of a degree-ten source, `z²` coefficient -/

section AffineDecic610Eighth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z²` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff2_610
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 2 =
      45 * r ^ 8 - 36 * (p.coeff 9 / h ^ 9) * r ^ 7 +
        28 * (p.coeff 8 / h ^ 8) * r ^ 6 -
        21 * (p.coeff 7 / h ^ 7) * r ^ 5 +
        15 * (p.coeff 6 / h ^ 6) * r ^ 4 -
        10 * (p.coeff 5 / h ^ 5) * r ^ 3 +
        6 * (p.coeff 4 / h ^ 4) * r ^ 2 -
        3 * (p.coeff 3 / h ^ 3) * r + p.coeff 2 / h ^ 2 := by
  let plow : (RatFunc k)[X] :=
    p - Polynomial.C (p.coeff 10) * Polynomial.X ^ 10 - Polynomial.C (p.coeff 9) * Polynomial.X ^ 9 -
      Polynomial.C (p.coeff 8) * Polynomial.X ^ 8 - Polynomial.C (p.coeff 7) * Polynomial.X ^ 7 -
      Polynomial.C (p.coeff 6) * Polynomial.X ^ 6 - Polynomial.C (p.coeff 5) * Polynomial.X ^ 5 -
      Polynomial.C (p.coeff 4) * Polynomial.X ^ 4 - Polynomial.C (p.coeff 3) * Polynomial.X ^ 3 -
      Polynomial.C (p.coeff 2) * Polynomial.X ^ 2
  have hplow : ∀ n, 2 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h2 | hlt2
    · subst n; simp
    · have : 3 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with h3 | hlt3
      · subst n; simp
      · have : 4 ≤ n := by omega
        rcases Nat.eq_or_lt_of_le this with h4 | hlt4
        · subst n; simp
        · have : 5 ≤ n := by omega
          rcases Nat.eq_or_lt_of_le this with h5 | hlt5
          · subst n; simp
          · have : 6 ≤ n := by omega
            rcases Nat.eq_or_lt_of_le this with h6 | hlt6
            · subst n; simp
            · have : 7 ≤ n := by omega
              rcases Nat.eq_or_lt_of_le this with h7 | hlt7
              · subst n; simp
              · have : 8 ≤ n := by omega
                rcases Nat.eq_or_lt_of_le this with h8 | hlt8
                · subst n; simp
                · have : 9 ≤ n := by omega
                  rcases Nat.eq_or_lt_of_le this with h9 | hlt9
                  · subst n; simp
                  · have : 10 ≤ n := by omega
                    rcases Nat.eq_or_lt_of_le this with h10 | hlt10
                    · subst n
                      simp [hp10, Polynomial.coeff_C_mul,
                        Polynomial.coeff_X_pow]
                    · simp [hp_high n (by omega), show n ≠ 10 by omega,
                        show n ≠ 9 by omega, show n ≠ 8 by omega,
                        show n ≠ 7 by omega, show n ≠ 6 by omega,
                        show n ≠ 5 by omega, show n ≠ 4 by omega,
                        show n ≠ 3 by omega, show n ≠ 2 by omega]
  have hplowDeg : plow.natDegree ≤ 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = Polynomial.C (p.coeff 10) * Polynomial.X ^ 10 + Polynomial.C (p.coeff 9) * Polynomial.X ^ 9 +
        Polynomial.C (p.coeff 8) * Polynomial.X ^ 8 + Polynomial.C (p.coeff 7) * Polynomial.X ^ 7 +
        Polynomial.C (p.coeff 6) * Polynomial.X ^ 6 + Polynomial.C (p.coeff 5) * Polynomial.X ^ 5 +
        Polynomial.C (p.coeff 4) * Polynomial.X ^ 4 + Polynomial.C (p.coeff 3) * Polynomial.X ^ 3 +
        Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 + plow := by
    simp only [plow]; ring
  have hq :
      affineDepress68 h r p =
        (Polynomial.C (p.coeff 10) * Polynomial.X ^ 10).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 9) * Polynomial.X ^ 9).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 8) * Polynomial.X ^ 8).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 7) * Polynomial.X ^ 7).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 6) * Polynomial.X ^ 6).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 5) * Polynomial.X ^ 5).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 4) * Polynomial.X ^ 4).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 3) * Polynomial.X ^ 3).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          (Polynomial.C (p.coeff 2) * Polynomial.X ^ 2).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) := rfl
    have hsum (A B D E G H I J K s t : (RatFunc k)[X]) :
        (A + B + D + E + G + H + I + J + K + s).comp t =
          A.comp t + B.comp t + D.comp t + E.comp t + G.comp t +
            H.comp t + I.comp t + J.comp t + K.comp t + s.comp t := by
      have h1 : (A + B + D + E + G + H + I + J + K + s).comp t =
          (A + B + D + E + G + H + I + J + K).comp t + s.comp t :=
        add_comp
      have h2 : (A + B + D + E + G + H + I + J + K).comp t =
          (A + B + D + E + G + H + I + J).comp t + K.comp t := add_comp
      have h3 : (A + B + D + E + G + H + I + J).comp t =
          (A + B + D + E + G + H + I).comp t + J.comp t := add_comp
      have h4 : (A + B + D + E + G + H + I).comp t =
          (A + B + D + E + G + H).comp t + I.comp t := add_comp
      have h5 : (A + B + D + E + G + H).comp t =
          (A + B + D + E + G).comp t + H.comp t := add_comp
      have h6 : (A + B + D + E + G).comp t =
          (A + B + D + E).comp t + G.comp t := add_comp
      have h7 : (A + B + D + E).comp t =
          (A + B + D).comp t + E.comp t := add_comp
      have h8 : (A + B + D).comp t = (A + B).comp t + D.comp t := add_comp
      have h9 : (A + B).comp t = A.comp t + B.comp t := add_comp
      rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]
    exact hdef.trans ((congrArg (fun t => t.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _ _ _ _ _ _))
  have hlow (n : ℕ) (hn : 2 ≤ n) :
      (plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle :
        (plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).natDegree ≤
          plow.natDegree * ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹).natDegree :=
      Polynomial.natDegree_comp_le
    have hdeg : ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹).natDegree = 1 :=
      natDegree_affineScale810 h r hh
    have hprod : plow.natDegree * ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹).natDegree ≤ 1 := by
      rw [hdeg, mul_one]
      exact hplowDeg
    have hcompDeg : (plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).natDegree ≤ 1 :=
      le_trans hle hprod
    exact Nat.lt_of_le_of_lt hcompDeg (Nat.lt_of_succ_le (by omega : 2 ≤ n))
  have h10_2 :
      ((Polynomial.C (p.coeff 10) * Polynomial.X ^ 10).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 2 =
        45 * r ^ 8 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 2 hh]
    have hle : (2 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 2 = 45 := by decide
    simp only [hle, ite_true, hp10, hbin]
    field_simp [hh]; ring
  have h9_2 :
      ((Polynomial.C (p.coeff 9) * Polynomial.X ^ 9).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 2 =
        -36 * (p.coeff 9 / h ^ 9) * r ^ 7 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 2 hh]
    have hle : (2 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 2 = 36 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h8_2 :
      ((Polynomial.C (p.coeff 8) * Polynomial.X ^ 8).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 2 =
        28 * (p.coeff 8 / h ^ 8) * r ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 2 hh]
    have hle : (2 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 2 = 28 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h7_2 :
      ((Polynomial.C (p.coeff 7) * Polynomial.X ^ 7).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 2 =
        -21 * (p.coeff 7 / h ^ 7) * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 2 hh]
    have hle : (2 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 2 = 21 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h6_2 :
      ((Polynomial.C (p.coeff 6) * Polynomial.X ^ 6).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 2 =
        15 * (p.coeff 6 / h ^ 6) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 2 hh]
    have hle : (2 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 2 = 15 := by decide
    simp only [hle, ite_true, hbin]
    field_simp [hh]; ring
  have h5_2 :
      ((Polynomial.C (p.coeff 5) * Polynomial.X ^ 5).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 2 =
        -10 * (p.coeff 5 / h ^ 5) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 2 hh]
    have hle : (2 : ℕ) ≤ 5 := by omega
    have hbin : (5 : ℕ).choose 2 = 10 := by decide
    simp only [hle, ite_true, hbin, pow_three]
    field_simp [hh]; ring
  have h4_2 :
      ((Polynomial.C (p.coeff 4) * Polynomial.X ^ 4).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 2 =
        6 * (p.coeff 4 / h ^ 4) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 4) h r 4 2 hh]
    have hle : (2 : ℕ) ≤ 4 := by omega
    have hbin : (4 : ℕ).choose 2 = 6 := by decide
    simp only [hle, ite_true, hbin, pow_two]
    field_simp [hh]; ring
  have h3_2 :
      ((Polynomial.C (p.coeff 3) * Polynomial.X ^ 3).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 2 =
        -3 * (p.coeff 3 / h ^ 3) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 3) h r 3 2 hh]
    have hle : (2 : ℕ) ≤ 3 := by omega
    have hbin : (3 : ℕ).choose 2 = 3 := by decide
    simp only [hle, ite_true, hbin, pow_one]
    field_simp [hh]; ring
  have h2_2 :
      ((Polynomial.C (p.coeff 2) * Polynomial.X ^ 2).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 2 =
        p.coeff 2 / h ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 2) h r 2 2 hh]
    simp [Nat.choose_self, pow_zero]
    field_simp [hh]
  rw [hq, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add, h10_2,
    h9_2, h8_2, h7_2, h6_2, h5_2, h4_2, h3_2, h2_2, hlow 2 (by omega)]
  ring

end AffineDecic610Eighth




section NonzeroEighthDefect610

variable {k : Type*} [Field k] [CharZero k]

/-- The seventh sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁴⁰`. -/
theorem nonzeroFace610_eighthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ eta : k,
      localClearedEighthDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          lambda =
        Polynomial.C eta * h0 ^ 40 := by
  let hRF : RatFunc k := algebraMap k[X] (RatFunc k) h0
  let a5 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 5)
  let a4 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 4)
  let a3 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 3)
  let a2 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 2)
  let a1 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 1)
  let a0 : RatFunc k := algebraMap k[X] (RatFunc k) (p.coeff 0)
  let b9 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 9)
  let b8 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 8)
  let b7 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 7)
  let b6 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 6)
  let b5 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 5)
  let b4 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 4)
  let b3 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 3)
  let b2 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 2)
  have hh : hRF ≠ 0 := RatFunc.algebraMap_ne_zero hh0
  have hpTop : algebraMap k[X] (RatFunc k) (p.coeff 6) = hRF ^ 6 := by
    simp only [hp6, hH, hRF, map_pow]
    ring
  have hqTop : algebraMap k[X] (RatFunc k) (q.coeff 10) = hRF ^ 10 := by
    simp only [hq10, hH, hRF, map_pow]
    ring
  have hpDep := affineDepress_sourceSextic68 p hRF
    (sexticDepressionR610 hRF a5) hp hh hpTop rfl
  have hNrat : 5 * a5 * hRF ^ 4 - 3 * b9 = RatFunc.C lambda * hRF ^ 9 := by
    have hmapped := congrArg (algebraMap k[X] (RatFunc k)) hN
    have hH2 : algebraMap k[X] (RatFunc k) (H ^ 2) = hRF ^ 4 := by
      simp only [hH, hRF, map_pow]
      ring
    have hh9 : algebraMap k[X] (RatFunc k) (h0 ^ 9) = hRF ^ 9 := by
      simp only [hRF, map_pow]
    have hleft : algebraMap k[X] (RatFunc k)
        ((5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9) =
        5 * a5 * hRF ^ 4 - 3 * b9 := by
      simp only [map_sub, map_mul, map_ofNat, a5, b9, hH2]
    have hright : algebraMap k[X] (RatFunc k)
        (Polynomial.C lambda * h0 ^ 9) =
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
  let f : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 p)
  let g : (RatFunc k)[X] :=
    affineDepress68 hRF (sexticDepressionR610 hRF a5) (sourceToRatFunc68 q)
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
  have hg_high_src : ∀ n, 10 < n → (sourceToRatFunc68 q).coeff n = 0 := by
    intro n hn
    simp [sourceToRatFunc68, sourceToRatFunc46,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]
  have hgTop : (sourceToRatFunc68 q).coeff 10 = hRF ^ 10 := by
    simpa [sourceToRatFunc68, sourceToRatFunc46] using hqTop
  obtain ⟨hg10, hg9, hg8, hg_high⟩ :=
    affineDepress_degreeTen_highCoeffs810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src
  have hg7 :
      g.coeff 7 =
        depressedQ610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff7_810 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedQ610, depressedQ810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8, b7]
  have hg6 :
      g.coeff 6 =
        depressedR610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff6_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedR610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6]
  have hg5 :
      g.coeff 5 =
        depressedS610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6
          b5 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff5_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedS610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5]
  have hg4 :
      g.coeff 4 =
        depressedT610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff4_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedT610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4]
  have hg2 :
      g.coeff 2 =
        depressedV610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 b2 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff2_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedV610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2]
  have hg8' :
      g.coeff 8 =
        depressedP610 hRF (sexticDepressionR610 hRF a5) b9 b8 := by
    dsimp only [g]
    rw [hg8]
    simp [depressedP610, depressedP810, sexticDepressionR610,
      sourceToRatFunc68, sourceToRatFunc46, b9, b8]
  have hg9' : g.coeff 9 = RatFunc.C (-lambda / 3) := by
    dsimp only [g]
    rw [hg9]
    have : -10 * sexticDepressionR610 hRF a5 +
        (sourceToRatFunc68 q).coeff 9 / hRF ^ 9 =
          depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    rw [this, hLval]
  have hLconst : ratFuncDerivation68 (g.coeff 9) = 0 := by
    rw [hg9']
    have hx := ratFuncDerivation46_polynomial (C (-lambda / 3) : k[X])
    simpa [ratFuncDerivation68, RatFunc.algebraMap_C] using hx
  have hrow13 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 4) -
        (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 8) = 0 := by
    have hrow :=
      differentialJacobian_coeff_13_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 13) hbracket
    simpa [f, g, Polynomial.coeff_C, show (13 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow12 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 3) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 4) -
        (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 7) = 0 := by
    have hrow :=
      differentialJacobian_coeff_12_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 12) hbracket
    simpa [f, g, Polynomial.coeff_C, show (12 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow11 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 2) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 3) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 4) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 8) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 6) = 0 := by
    have hrow :=
      differentialJacobian_coeff_11_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 11) hbracket
    simpa [f, g, Polynomial.coeff_C, show (11 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow10 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 1) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 2) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 3) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 4) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 8) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 7) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 5) = 0 := by
    have hrow :=
      differentialJacobian_coeff_10_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 10) hbracket
    simpa [f, g, Polynomial.coeff_C, show (10 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow9 :
      (10 : RatFunc k) * ratFuncDerivation68 (f.coeff 0) +
          (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 1) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 2) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 3) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 4) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 8) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 7) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 6) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 4) = 0 := by
    have hrow :=
      differentialJacobian_coeff_9_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 9) hbracket
    simpa [f, g, Polynomial.coeff_C, show (9 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow7 :
      (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 0) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 1) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 2) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 3) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 7) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 6) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 5) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 4) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 2) = 0 := by
    have hrow :=
      differentialJacobian_coeff_7_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 7) hbracket
    simpa [f, g, Polynomial.coeff_C, show (7 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hf4 : f.coeff 4 =
      depressedA610 hRF (sexticDepressionR610 hRF a5) a5 a4 := by
    dsimp only [f, depressedA610, a5, a4]
    rw [hpDep, coeff_depressedSextic68_four]
  have hf3 : f.coeff 3 =
      depressedB610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 := by
    dsimp only [f, depressedB610, a5, a4, a3]
    rw [hpDep, coeff_depressedSextic68_three]
  have hf2 : f.coeff 2 =
      depressedC610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 := by
    dsimp only [f, depressedC610, a5, a4, a3, a2]
    rw [hpDep, coeff_depressedSextic68_two]
  have hf1 : f.coeff 1 =
      depressedD610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1 := by
    dsimp only [f, depressedD610, a5, a4, a3, a2, a1]
    rw [hpDep, coeff_depressedSextic68_one]
  have hf0 : f.coeff 0 =
      depressedE610 hRF (sexticDepressionR610 hRF a5) a5 a4 a3 a2 a1
        a0 := by
    dsimp only [f, depressedE610, a5, a4, a3, a2, a1, a0]
    rw [hpDep, coeff_depressedSextic68_zero]
  have halpha0 :
      ratFuncDerivation68 (alphaResidual610 (f.coeff 4) (g.coeff 8)) = 0 :=
    alphaResidual610_deriv_zero ratFuncDerivation68 (f.coeff 4)
      (g.coeff 8) hrow13
  have hbeta0 :
      ratFuncDerivation68
        (betaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (g.coeff 7)) = 0 :=
    betaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (g.coeff 7) hLconst (by simpa using hrow12)
  have hgamma0 :
      ratFuncDerivation68
        (gammaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (g.coeff 8) (g.coeff 6)) = 0 :=
    gammaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (g.coeff 8) (g.coeff 6)
      hLconst halpha0 (by simpa using hrow11)
  have hdelta0 :
      ratFuncDerivation68
        (deltaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (g.coeff 8) (g.coeff 7)
          (g.coeff 5)) = 0 :=
    deltaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (g.coeff 8)
      (g.coeff 7) (g.coeff 5) hLconst halpha0 hbeta0
      (by simpa using hrow10)
  have heps0deriv :
      ratFuncDerivation68
        (epsilonResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 4)) = 0 :=
    epsilonResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 4) hLconst halpha0
      hbeta0 hgamma0 (by simpa using hrow9)
  have heta0deriv :
      ratFuncDerivation68
        (etaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2)) = 0 :=
    etaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 2) hLconst halpha0 hbeta0 hgamma0 hdelta0 heps0deriv
      (by simpa using hrow7)
  obtain ⟨eta0, heta0⟩ :
      ∃ a : k,
        etaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      heta0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedEighthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) lambda) =
        (118098 : RatFunc k) * hRF ^ 40 *
          etaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 2) := by
    have hF := eighthDefect_eq_clearedEta610 hRF a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 (RatFunc.C lambda) hh
      (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedEighthDefect610, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3, a2, a1, a0,
      b8, b7, b6, b5, b4, b3, b2, etaResidual610, alphaResidual610,
      betaResidual610, gammaResidual610, deltaResidual610,
      epsilonResidual610, hf4, hf3, hf2, hf1, hf0, hg2, hg4, hg5, hg6,
      hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedEighthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (118098 * eta0) * h0 ^ 40) := by
    rw [hclear, heta0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨118098 * eta0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget
end NonzeroEighthDefect610


variable [IsAlgClosed k]

/-- Strongest exact seventh residual after the constant-scale source bridge:
the cleared weight-forty sextic/decic defect is a scalar times `h⁴⁰`.
Both the vanishing and the nonzero values of `λ` are permitted. -/
theorem scaleZero_seventhClearedDefect_exists_C_610
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda alpha gamma delta eps zeta eta theta : k),
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
        Polynomial.C eta * (Polynomial.C t) ^ 35 ∧
      localClearedEighthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) lambda =
        Polynomial.C theta * (Polynomial.C t) ^ 40 := by
  obtain ⟨lambda, alpha, gamma, delta, eps, zeta, eta, hN, halpha, hgamma,
      hdelta, heps, hzeta, heta⟩ :=
    scaleZero_sixthClearedDefect_exists_C_610 hp hq hD ht hH hp6 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨theta, htheta⟩ :=
    nonzeroFace610_eighthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  exact ⟨lambda, alpha, gamma, delta, eps, zeta, eta, theta, hN, halpha,
    hgamma, hdelta, heps, hzeta, heta, htheta⟩

/-- Source-facing seventh residual packet for a normalized scale-zero
`(6,10)` pair.  The constants `λ`, `α`, `γ`, `δ`, `ε`, `ζ`, `η`, and
`θ` may vanish. -/
theorem normalized610ScaleZero_exists_seventhClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda alpha gamma delta eps zeta eta theta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedEighthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C theta * (Polynomial.C t) ^ 40 := by
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
  obtain ⟨lambda, _alpha, _gamma, _delta, _eps, _zeta, _eta, theta, hN,
      _hM, _hT, _hU, _hV, _hW, _hX, hY⟩ :=
    scaleZero_seventhClearedDefect_exists_C_610 hp hq hD ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  exact ⟨t, lambda, 0, 0, 0, 0, 0, 0, theta, ht, hHsq,
    by simpa only [p, q] using hN,
    by simpa only [p, q] using hY⟩

/-- At scale zero the weight-forty defect is a literal ground-field
constant. -/
theorem normalized610ScaleZero_seventhClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda theta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedEighthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C theta := by
  obtain ⟨t, lambda, _a, _g, _d, _e, _z, _et, theta, ht, hHsq, _hN, hY⟩ :=
    normalized610ScaleZero_exists_seventhClearedDefect hsource
  refine ⟨t, lambda, theta * t ^ 40, ht, hHsq, ?_⟩
  have hconst :
      localClearedEighthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C (theta * t ^ 40) := by
    rw [hY, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) theta (t ^ 40)).symm
  exact hconst

/-- Newton degree of the seventh cleared sextic/decic defect at scale zero. -/
theorem normalized610ScaleZero_seventhClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedEighthDefect610 (Polynomial.C t)
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
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, theta, ht, hHsq, hY⟩ :=
    normalized610ScaleZero_seventhClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hY]
  exact (natDegree_C theta).le

/-- Exact seventh residual selector: `118098 q₂ h³⁸` differs from a
polynomial in the remaining eighth-defect monomials by a ground constant. -/
theorem normalized610ScaleZero_seventhSourceResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda theta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (118098 : k[X]) * q.coeff 2 * h0 ^ 38 =
        Polynomial.C theta -
          (localClearedEighthDefect610 h0 (p.coeff 5) (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
              (q.coeff 4) (q.coeff 3) (q.coeff 2) lambda -
            (118098 : k[X]) * q.coeff 2 * h0 ^ 38) := by
  dsimp only
  obtain ⟨t, lambda, theta, ht, hHsq, hY⟩ :=
    normalized610ScaleZero_seventhClearedDefect_exists_C hsource
  refine ⟨t, lambda, theta, ht, hHsq, ?_⟩
  have hX := hY
  simp only [localClearedEighthDefect610] at hX ⊢
  linear_combination hX

/-- Aligned/nonzero split of the scale-zero seventh cleared defect: it
vanishes, or it is a nonzero ground-field constant. -/
theorem normalized610ScaleZero_seventhClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let W :=
        localClearedEighthDefect610 (Polynomial.C t)
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
          lambda
      W = 0 ∨ ∃ theta : k, theta ≠ 0 ∧ W = Polynomial.C theta := by
  dsimp only
  obtain ⟨t, lambda, theta, ht, hHsq, hY⟩ :=
    normalized610ScaleZero_seventhClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  by_cases htheta : theta = 0
  · left
    simpa only [htheta, Polynomial.C_0] using hY
  · exact Or.inr ⟨theta, htheta, hY⟩

/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-forty defect. -/
theorem normalized610ScaleZero_seventhClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda theta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9
      let W :=
        localClearedEighthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      W = Polynomial.C theta ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (theta = 0 ∧ W = 0 ∨
        theta ≠ 0 ∧ W = Polynomial.C theta) := by
  dsimp only
  obtain ⟨t, lambda, _a, _g, _d, _e, _z, _et, theta0, ht, hHsq, hN, hYpow⟩ :=
    normalized610ScaleZero_exists_seventhClearedDefect hsource
  let theta : k := theta0 * t ^ 40
  have hY :
      localClearedEighthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C theta := by
    rw [hYpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) theta0 (t ^ 40)).symm
  refine ⟨t, lambda, theta, ht, hHsq, hN, hY, ?_, ?_⟩
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
  · by_cases htheta : theta = 0
    · left
      refine ⟨htheta, ?_⟩
      simpa only [htheta, Polynomial.C_0] using hY
    · exact Or.inr ⟨htheta, hY⟩

/-- Aligned branch `N = 0`: the weight-forty defect is still a ground
constant, now with `λ = 0`. -/
theorem normalized610ScaleZero_seventhClearedDefect_of_aligned
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (haligned :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t theta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedEighthDefect610 (Polynomial.C t)
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
          0 =
        Polynomial.C theta := by
  obtain ⟨t, lambda, _a, _g, _d, _e, _z, _et, theta0, ht, hHsq, hN, hYpow⟩ :=
    normalized610ScaleZero_exists_seventhClearedDefect hsource
  have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
    pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
  have hlambda : lambda = 0 := by
    have hmul : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
      hN.symm.trans haligned
    have hC : Polynomial.C lambda = 0 :=
      (mul_eq_zero.mp hmul).resolve_right ht9
    exact Polynomial.C_eq_zero.mp hC
  refine ⟨t, theta0 * t ^ 40, ht, hHsq, ?_⟩
  have hY :
      localClearedEighthDefect610 (Polynomial.C t)
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
          0 =
        Polynomial.C (theta0 * t ^ 40) := by
    rw [← hlambda, hYpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) theta0 (t ^ 40)).symm
  exact hY

/-- Nonzero discriminator branch: `λ ≠ 0` and the weight-forty defect
is still a ground constant. -/
theorem normalized610ScaleZero_seventhClearedDefect_of_nonzero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (hnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda theta : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedEighthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C theta := by
  obtain ⟨t, lambda, _a, _g, _d, _e, _z, _et, theta0, ht, hHsq, hN, hYpow⟩ :=
    normalized610ScaleZero_exists_seventhClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro hzero
    apply hnonzero
    simpa only [hzero, Polynomial.C_0, zero_mul] using hN
  refine ⟨t, lambda, theta0 * t ^ 40, ht, hlambda, hHsq, hN, ?_⟩
  have hY :
      localClearedEighthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C (theta0 * t ^ 40) := by
    rw [hYpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) theta0 (t ^ 40)).symm
  exact hY

end ScaleZeroSeventhDefect610

#print axioms normalized610ScaleZero_eighthCoefficientJacobianRow
#print axioms scaleZero_eighthCoefficientJacobianRow_610
#print axioms normalized610ScaleZero_eighthCoefficientJacobianRow_collapsed
#print axioms depressedV610_eq_cleared
#print axioms eighthDefect_eq_clearedEta610
#print axioms differentialJacobian_coeff_7_monicSexticDecic
#print axioms etaResidual610_deriv_zero
#print axioms affineDepress_degreeTen_coeff2_610
#print axioms nonzeroFace610_eighthDefectPowerRelation
#print axioms scaleZero_seventhClearedDefect_exists_C_610
#print axioms localClearedEighthDefect610_of_lambda_zero
#print axioms normalized610ScaleZero_exists_seventhClearedDefect
#print axioms normalized610ScaleZero_seventhClearedDefect_exists_C
#print axioms normalized610ScaleZero_seventhClearedDefect_natDegree_le_zero
#print axioms normalized610ScaleZero_seventhSourceResidual
#print axioms normalized610ScaleZero_seventhClearedDefectFirstFace
#print axioms normalized610ScaleZero_seventhClearedDefectBranches
#print axioms normalized610ScaleZero_seventhClearedDefect_of_aligned
#print axioms normalized610ScaleZero_seventhClearedDefect_of_nonzero

end Max11DegreeRoutes
