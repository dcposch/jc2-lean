import Grok610ScaleZeroEighthDefectScratch

/-! # Scale-zero ninth cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroEighthDefectScratch` on the constant core
`H = (C t)²`.  The eighth packet already forces the discriminator `N` and
the weight-forty-five defect `Z` to ground constants.  This file consumes
the next unused Keller coefficient, the degree-`5` Jacobian row

```
(p₅)' (1 q₁) + (p₄)' (2 q₂) + (p₃)' (3 q₃) + (p₂)' (4 q₄) + (p₁)' (5 q₅)
  + (p₀)' (6 q₆)
  - (6 p₆) q₀' - (5 p₅) q₁' - (4 p₄) q₂' - (3 p₃) q₃' - (2 p₂) q₄'
  - (1 p₁) q₅' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is
`6 R E' + 5 S D' + 4 T C' + 3 U B' + 2 V A' - D S' - 2 C T' - 3 B U'
- 4 A V' - 6 X' = 0`.  The corresponding first integral clears to the
weight-fifty polynomial defect, and at scale zero that defect is again a
ground-field constant.

No total-degree or twice-prime theorem is used.  A constant scale has no
finite root, so the scale-two tenth-face jet is unavailable.  Both the
vanishing and the nonzero constant branches of `λ` and of the weight-fifty
defect are kept.  The packet does not close the leaf: unused Jacobian
coefficients start at degree `4`.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000

section ScaleZeroNinthDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/

/-- The tenth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  Unused Jacobian coefficients of the eighth packet
start at degree `5`. -/
theorem scaleZeroRaw_tenthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 5).derivative * q.coeff 1 +
        (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : K)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : K)) -
      ((p.coeff 6 * Polynomial.C (6 : K)) * (q.coeff 0).derivative +
        (p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 1).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 5) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (5 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 5 :
      Finset (ℕ × ℕ)) =
      ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1),
        (5, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  have hC5 : Polynomial.C (5 : K) = (5 : K[X]) :=
    Polynomial.C_eq_natCast 5
  have hC6 : Polynomial.C (6 : K) = (6 : K[X]) :=
    Polynomial.C_eq_natCast 6
  rw [hC2, hC3, hC4, hC5, hC6]
  linear_combination hcoeff

/-- Source-facing degree-`5` Jacobian row of a normalized scale-zero
`(6,10)` pair. -/
theorem normalized610ScaleZero_tenthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 5).derivative * q.coeff 1 +
        (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 0).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 1).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) =
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
  simpa only [p, q] using
    scaleZeroRaw_tenthCoefficientJacobianRow_610 hp hq hjac

/-- At scale zero the common core is constant, so the leading sextic
coefficient of the degree-`5` row is a differential constant.  The row
itself has no `p₆'` term. -/
theorem scaleZero_tenthCoefficientJacobianRow_610
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 5).derivative * q.coeff 1 +
        (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 0).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 1).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp6der : (p.coeff 6).derivative = 0 := by
    rw [hp6, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := scaleZeroRaw_tenthCoefficientJacobianRow_610 hp hq hjac
  simpa [hp6der, hq10der] using hrow

/-- Source-facing scale-zero collapse of the degree-`5` row. -/
theorem normalized610ScaleZero_tenthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 5).derivative * q.coeff 1 +
        (p.coeff 4).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 3).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 2).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 1).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 0).derivative * (q.coeff 6 * Polynomial.C (6 : k)) -
      ((p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 0).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 1).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 2).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 3).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 4).derivative +
        p.coeff 1 * (q.coeff 5).derivative) =
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
    scaleZero_tenthCoefficientJacobianRow_610 hp hq hjac hHdegree
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)

/-! ## Weight-fifty cleared defect after a square root of the core -/

section Depression610Tenth

variable {F : Type*} [Field F] [CharZero F]

/-- Depressed decic `z⁰` coefficient. -/
def depressedX610 (h r b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 : F) : F :=
  r ^ 10 - (b9 / h ^ 9) * r ^ 9 + (b8 / h ^ 8) * r ^ 8 -
    (b7 / h ^ 7) * r ^ 7 + (b6 / h ^ 6) * r ^ 6 -
    (b5 / h ^ 5) * r ^ 5 + (b4 / h ^ 4) * r ^ 4 -
    (b3 / h ^ 3) * r ^ 3 + (b2 / h ^ 2) * r ^ 2 -
    (b1 / h) * r + b0

/-- First residual of the degree-`5` row.  Equivalent to
`X - γ E - (5/6) δ D - (2/3) ε C - (1/2) ζ B - (1/3) η A
- (10/9) C E - (5/9) D² + (5/27) A² E + (10/27) A B D + (5/27) A C²
+ (5/27) B² C - (10/81) A² B² - (20/243) A³ C + (7/729) A⁵
- (4/9) α A E - (4/9) α B D - (2/9) α C² + (4/27) α A² C
+ (4/27) α A B² - (5/243) α A⁴ - (7/36) β A D - (7/36) β B C
+ (35/432) β A² B + (5/36) δ A B + (1/9) ε A²
- (3/4) L B E - (3/4) L C D + (3/8) L A B C + (3/16) L A² D
+ (1/16) L B³ - (3/32) L A³ B`
on the second- through eighth-face integrals. -/
def iotaResidual610
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 X0 : F) : F :=
  X0 - gammaResidual610 L A B C0 P R * E0 -
    (5 / 6 : F) * deltaResidual610 L A B C0 D0 P Q S0 * D0 -
    (2 / 3 : F) * epsilonResidual610 L A B C0 D0 E0 P Q R T0 * C0 -
    (1 / 2 : F) * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 * B -
    (1 / 3 : F) * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 * A -
    (10 / 9 : F) * C0 * E0 - (5 / 9 : F) * D0 ^ 2 +
    (5 / 27 : F) * A ^ 2 * E0 + (10 / 27 : F) * A * B * D0 +
    (5 / 27 : F) * A * C0 ^ 2 + (5 / 27 : F) * B ^ 2 * C0 -
    (10 / 81 : F) * A ^ 2 * B ^ 2 - (20 / 243 : F) * A ^ 3 * C0 +
    (7 / 729 : F) * A ^ 5 -
    (4 / 9 : F) * alphaResidual610 A P * A * E0 -
    (4 / 9 : F) * alphaResidual610 A P * B * D0 -
    (2 / 9 : F) * alphaResidual610 A P * C0 ^ 2 +
    (4 / 27 : F) * alphaResidual610 A P * A ^ 2 * C0 +
    (4 / 27 : F) * alphaResidual610 A P * A * B ^ 2 -
    (5 / 243 : F) * alphaResidual610 A P * A ^ 4 -
    (7 / 36 : F) * betaResidual610 L A B Q * A * D0 -
    (7 / 36 : F) * betaResidual610 L A B Q * B * C0 +
    (35 / 432 : F) * betaResidual610 L A B Q * A ^ 2 * B +
    (5 / 36 : F) * deltaResidual610 L A B C0 D0 P Q S0 * A * B +
    (1 / 9 : F) * epsilonResidual610 L A B C0 D0 E0 P Q R T0 * A ^ 2 -
    (3 / 4 : F) * L * B * E0 - (3 / 4 : F) * L * C0 * D0 +
    (3 / 8 : F) * L * A * B * C0 + (3 / 16 : F) * L * A ^ 2 * D0 +
    (1 / 16 : F) * L * B ^ 3 - (3 / 32 : F) * L * A ^ 3 * B

set_option maxHeartbeats 8000000 in
/-- Polynomial numerator of `18 h⁵⁰ ι` on the ninth-power face. -/
def localClearedTenthDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 b0 : F[X]) (lambda : F) : F[X] :=
    (30 : F[X]) * a0 * a2 * h ^ 48
    - (15 : F[X]) * a0 * a3 * a5 * h ^ 42
    - (9 : F[X]) * a0 * a3 * h ^ 47 * Polynomial.C lambda
    - (30 : F[X]) * a0 * a4 ^ 2 * h ^ 42
    + (18 : F[X]) * a0 * a4 * a5 * h ^ 41 * Polynomial.C lambda
    + (24 : F[X]) * a0 * a4 * b8 * h ^ 38
    + (15 : F[X]) * a0 * a5 ^ 4 * h ^ 30
    - (9 : F[X]) * a0 * a5 ^ 3 * h ^ 35 * Polynomial.C lambda
    - (24 : F[X]) * a0 * a5 ^ 2 * b8 * h ^ 32
    + (21 : F[X]) * a0 * a5 * b7 * h ^ 38
    - (18 : F[X]) * a0 * b6 * h ^ 44
    + (15 : F[X]) * a1 ^ 2 * h ^ 48
    - (15 : F[X]) * a1 * a2 * a5 * h ^ 42
    - (9 : F[X]) * a1 * a2 * h ^ 47 * Polynomial.C lambda
    - (60 : F[X]) * a1 * a3 * a4 * h ^ 42
    + (18 : F[X]) * a1 * a3 * a5 * h ^ 41 * Polynomial.C lambda
    + (24 : F[X]) * a1 * a3 * b8 * h ^ 38
    + (45 : F[X]) * a1 * a4 ^ 2 * a5 * h ^ 36
    + (9 : F[X]) * a1 * a4 ^ 2 * h ^ 41 * Polynomial.C lambda
    + (15 : F[X]) * a1 * a4 * a5 ^ 3 * h ^ 30
    - (27 : F[X]) * a1 * a4 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    - (48 : F[X]) * a1 * a4 * a5 * b8 * h ^ 32
    + (21 : F[X]) * a1 * a4 * b7 * h ^ 38
    - (15 : F[X]) * a1 * a5 ^ 5 * h ^ 24
    + (9 : F[X]) * a1 * a5 ^ 4 * h ^ 29 * Polynomial.C lambda
    + (24 : F[X]) * a1 * a5 ^ 3 * b8 * h ^ 26
    - (21 : F[X]) * a1 * a5 ^ 2 * b7 * h ^ 32
    + (18 : F[X]) * a1 * a5 * b6 * h ^ 38
    - (15 : F[X]) * a1 * b5 * h ^ 44
    - (30 : F[X]) * a2 ^ 2 * a4 * h ^ 42
    + (9 : F[X]) * a2 ^ 2 * a5 * h ^ 41 * Polynomial.C lambda
    + (12 : F[X]) * a2 ^ 2 * b8 * h ^ 38
    - (30 : F[X]) * a2 * a3 ^ 2 * h ^ 42
    + (90 : F[X]) * a2 * a3 * a4 * a5 * h ^ 36
    + (18 : F[X]) * a2 * a3 * a4 * h ^ 41 * Polynomial.C lambda
    + (15 : F[X]) * a2 * a3 * a5 ^ 3 * h ^ 30
    - (27 : F[X]) * a2 * a3 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    - (48 : F[X]) * a2 * a3 * a5 * b8 * h ^ 32
    + (21 : F[X]) * a2 * a3 * b7 * h ^ 38
    + (30 : F[X]) * a2 * a4 ^ 3 * h ^ 36
    - (45 : F[X]) * a2 * a4 ^ 2 * a5 ^ 2 * h ^ 30
    - (27 : F[X]) * a2 * a4 ^ 2 * a5 * h ^ 35 * Polynomial.C lambda
    - (24 : F[X]) * a2 * a4 ^ 2 * b8 * h ^ 32
    - (30 : F[X]) * a2 * a4 * a5 ^ 4 * h ^ 24
    + (36 : F[X]) * a2 * a4 * a5 ^ 3 * h ^ 29 * Polynomial.C lambda
    + (72 : F[X]) * a2 * a4 * a5 ^ 2 * b8 * h ^ 26
    - (42 : F[X]) * a2 * a4 * a5 * b7 * h ^ 32
    + (18 : F[X]) * a2 * a4 * b6 * h ^ 38
    + (15 : F[X]) * a2 * a5 ^ 6 * h ^ 18
    - (9 : F[X]) * a2 * a5 ^ 5 * h ^ 23 * Polynomial.C lambda
    - (24 : F[X]) * a2 * a5 ^ 4 * b8 * h ^ 20
    + (21 : F[X]) * a2 * a5 ^ 3 * b7 * h ^ 26
    - (18 : F[X]) * a2 * a5 ^ 2 * b6 * h ^ 32
    + (15 : F[X]) * a2 * a5 * b5 * h ^ 38
    - (12 : F[X]) * a2 * b4 * h ^ 44
    + (15 : F[X]) * a3 ^ 3 * a5 * h ^ 36
    + (3 : F[X]) * a3 ^ 3 * h ^ 41 * Polynomial.C lambda
    + (45 : F[X]) * a3 ^ 2 * a4 ^ 2 * h ^ 36
    - (45 : F[X]) * a3 ^ 2 * a4 * a5 ^ 2 * h ^ 30
    - (27 : F[X]) * a3 ^ 2 * a4 * a5 * h ^ 35 * Polynomial.C lambda
    - (24 : F[X]) * a3 ^ 2 * a4 * b8 * h ^ 32
    - (15 : F[X]) * a3 ^ 2 * a5 ^ 4 * h ^ 24
    + (18 : F[X]) * a3 ^ 2 * a5 ^ 3 * h ^ 29 * Polynomial.C lambda
    + (36 : F[X]) * a3 ^ 2 * a5 ^ 2 * b8 * h ^ 26
    - (21 : F[X]) * a3 ^ 2 * a5 * b7 * h ^ 32
    + (9 : F[X]) * a3 ^ 2 * b6 * h ^ 38
    - (75 : F[X]) * a3 * a4 ^ 3 * a5 * h ^ 30
    - (9 : F[X]) * a3 * a4 ^ 3 * h ^ 35 * Polynomial.C lambda
    + (30 : F[X]) * a3 * a4 ^ 2 * a5 ^ 3 * h ^ 24
    + (54 : F[X]) * a3 * a4 ^ 2 * a5 ^ 2 * h ^ 29 * Polynomial.C lambda
    + (72 : F[X]) * a3 * a4 ^ 2 * a5 * b8 * h ^ 26
    - (21 : F[X]) * a3 * a4 ^ 2 * b7 * h ^ 32
    + (45 : F[X]) * a3 * a4 * a5 ^ 5 * h ^ 18
    - (45 : F[X]) * a3 * a4 * a5 ^ 4 * h ^ 23 * Polynomial.C lambda
    - (96 : F[X]) * a3 * a4 * a5 ^ 3 * b8 * h ^ 20
    + (63 : F[X]) * a3 * a4 * a5 ^ 2 * b7 * h ^ 26
    - (36 : F[X]) * a3 * a4 * a5 * b6 * h ^ 32
    + (15 : F[X]) * a3 * a4 * b5 * h ^ 38
    - (15 : F[X]) * a3 * a5 ^ 7 * h ^ 12
    + (9 : F[X]) * a3 * a5 ^ 6 * h ^ 17 * Polynomial.C lambda
    + (24 : F[X]) * a3 * a5 ^ 5 * b8 * h ^ 14
    - (21 : F[X]) * a3 * a5 ^ 4 * b7 * h ^ 20
    + (18 : F[X]) * a3 * a5 ^ 3 * b6 * h ^ 26
    - (15 : F[X]) * a3 * a5 ^ 2 * b5 * h ^ 32
    + (12 : F[X]) * a3 * a5 * b4 * h ^ 38
    - (9 : F[X]) * a3 * b3 * h ^ 44
    - (6 : F[X]) * a4 ^ 5 * h ^ 30
    + (30 : F[X]) * a4 ^ 4 * a5 ^ 2 * h ^ 24
    + (9 : F[X]) * a4 ^ 4 * a5 * h ^ 29 * Polynomial.C lambda
    + (6 : F[X]) * a4 ^ 4 * b8 * h ^ 26
    - (30 : F[X]) * a4 ^ 3 * a5 ^ 3 * h ^ 23 * Polynomial.C lambda
    - (48 : F[X]) * a4 ^ 3 * a5 ^ 2 * b8 * h ^ 20
    + (21 : F[X]) * a4 ^ 3 * a5 * b7 * h ^ 26
    - (6 : F[X]) * a4 ^ 3 * b6 * h ^ 32
    - (30 : F[X]) * a4 ^ 2 * a5 ^ 6 * h ^ 12
    + (27 : F[X]) * a4 ^ 2 * a5 ^ 5 * h ^ 17 * Polynomial.C lambda
    + (60 : F[X]) * a4 ^ 2 * a5 ^ 4 * b8 * h ^ 14
    - (42 : F[X]) * a4 ^ 2 * a5 ^ 3 * b7 * h ^ 20
    + (27 : F[X]) * a4 ^ 2 * a5 ^ 2 * b6 * h ^ 26
    - (15 : F[X]) * a4 ^ 2 * a5 * b5 * h ^ 32
    + (6 : F[X]) * a4 ^ 2 * b4 * h ^ 38
    + (15 : F[X]) * a4 * a5 ^ 8 * h ^ 6
    - (9 : F[X]) * a4 * a5 ^ 7 * h ^ 11 * Polynomial.C lambda
    - (24 : F[X]) * a4 * a5 ^ 6 * b8 * h ^ 8
    + (21 : F[X]) * a4 * a5 ^ 5 * b7 * h ^ 14
    - (18 : F[X]) * a4 * a5 ^ 4 * b6 * h ^ 20
    + (15 : F[X]) * a4 * a5 ^ 3 * b5 * h ^ 26
    - (12 : F[X]) * a4 * a5 ^ 2 * b4 * h ^ 32
    + (9 : F[X]) * a4 * a5 * b3 * h ^ 38
    - (6 : F[X]) * a4 * b2 * h ^ 44
    - (2 : F[X]) * a5 ^ 10
    + (1 : F[X]) * a5 ^ 9 * h ^ 5 * Polynomial.C lambda
    + (3 : F[X]) * a5 ^ 8 * b8 * h ^ 2
    - (3 : F[X]) * a5 ^ 7 * b7 * h ^ 8
    + (3 : F[X]) * a5 ^ 6 * b6 * h ^ 14
    - (3 : F[X]) * a5 ^ 5 * b5 * h ^ 20
    + (3 : F[X]) * a5 ^ 4 * b4 * h ^ 26
    - (3 : F[X]) * a5 ^ 3 * b3 * h ^ 32
    + (3 : F[X]) * a5 ^ 2 * b2 * h ^ 38
    - (3 : F[X]) * a5 * b1 * h ^ 44
    + (18 : F[X]) * b0 * h ^ 50


/-- Exact denominator clearing for the decic `z⁰` coordinate on the
ninth-power face. -/
theorem depressedX610_eq_cleared
    (h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 lambda : F) (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    depressedX610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4 b3
        b2 b1 b0 =
      (-9 * a5 ^ 10 + 2 * lambda * a5 ^ 9 * h ^ 5 +
          36 * a5 ^ 8 * b8 * h ^ 2 - 216 * a5 ^ 7 * b7 * h ^ 8 +
          1296 * a5 ^ 6 * b6 * h ^ 14 - 7776 * a5 ^ 5 * b5 * h ^ 20 +
          46656 * a5 ^ 4 * b4 * h ^ 26 - 279936 * a5 ^ 3 * b3 * h ^ 32 +
          1679616 * a5 ^ 2 * b2 * h ^ 38 - 10077696 * a5 * b1 * h ^ 44 +
          60466176 * b0 * h ^ 50) /
        (60466176 * h ^ 50) := by
  have h6 : (6 : F) ≠ 0 := by norm_num
  have h3 : (3 : F) ≠ 0 := by norm_num
  have h60466176 : (60466176 : F) ≠ 0 := by norm_num
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  have hh4 : h ^ 4 ≠ 0 := pow_ne_zero 4 hh
  have hh5 : h ^ 5 ≠ 0 := pow_ne_zero 5 hh
  have hh6 : h ^ 6 ≠ 0 := pow_ne_zero 6 hh
  have hh7 : h ^ 7 ≠ 0 := pow_ne_zero 7 hh
  have hh8pow : h ^ 8 ≠ 0 := pow_ne_zero 8 hh
  have hh9 : h ^ 9 ≠ 0 := pow_ne_zero 9 hh
  have hh50 : h ^ 50 ≠ 0 := pow_ne_zero 50 hh
  have hb9 : 3 * b9 = 5 * a5 * h ^ 4 - lambda * h ^ 9 := by
    linear_combination -hN
  simp only [depressedX610, sexticDepressionR610, sexticDepressionR68]
  have hrewrite :
      (a5 / (6 * h ^ 5)) ^ 10 -
          (b9 / h ^ 9) * (a5 / (6 * h ^ 5)) ^ 9 +
        (b8 / h ^ 8) * (a5 / (6 * h ^ 5)) ^ 8 -
          (b7 / h ^ 7) * (a5 / (6 * h ^ 5)) ^ 7 +
        (b6 / h ^ 6) * (a5 / (6 * h ^ 5)) ^ 6 -
          (b5 / h ^ 5) * (a5 / (6 * h ^ 5)) ^ 5 +
        (b4 / h ^ 4) * (a5 / (6 * h ^ 5)) ^ 4 -
          (b3 / h ^ 3) * (a5 / (6 * h ^ 5)) ^ 3 +
        (b2 / h ^ 2) * (a5 / (6 * h ^ 5)) ^ 2 -
          (b1 / h) * (a5 / (6 * h ^ 5)) + b0 =
        (-9 * a5 ^ 10 + 2 * lambda * a5 ^ 9 * h ^ 5 +
            36 * a5 ^ 8 * b8 * h ^ 2 - 216 * a5 ^ 7 * b7 * h ^ 8 +
            1296 * a5 ^ 6 * b6 * h ^ 14 - 7776 * a5 ^ 5 * b5 * h ^ 20 +
            46656 * a5 ^ 4 * b4 * h ^ 26 - 279936 * a5 ^ 3 * b3 * h ^ 32 +
            1679616 * a5 ^ 2 * b2 * h ^ 38 - 10077696 * a5 * b1 * h ^ 44 +
            60466176 * b0 * h ^ 50) /
          (60466176 * h ^ 50) := by
    field_simp [hh, h6, h3, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh50, h60466176]
    have hb9' :
        b9 = (5 * a5 * h ^ 4 - lambda * h ^ 9) / 3 := by
      field_simp [h3]
      linear_combination hb9
    rw [hb9']
    field_simp [hh, h6, h3, hh2, hh3, hh4, hh5, hh6, hh7, hh8pow, hh9,
      hh50, h60466176]
    ring
  exact hrewrite

set_option maxHeartbeats 8000000 in
/-- Aligned specialization of the weight-fifty defect: the
`λ`-monomials drop. -/
theorem localClearedTenthDefect610_of_lambda_zero
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 b0 : F[X]) :
    localClearedTenthDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3
        b2 b1 b0 0 =
    (30 : F[X]) * a0 * a2 * h ^ 48
    - (15 : F[X]) * a0 * a3 * a5 * h ^ 42
    - (30 : F[X]) * a0 * a4 ^ 2 * h ^ 42
    + (24 : F[X]) * a0 * a4 * b8 * h ^ 38
    + (15 : F[X]) * a0 * a5 ^ 4 * h ^ 30
    - (24 : F[X]) * a0 * a5 ^ 2 * b8 * h ^ 32
    + (21 : F[X]) * a0 * a5 * b7 * h ^ 38
    - (18 : F[X]) * a0 * b6 * h ^ 44
    + (15 : F[X]) * a1 ^ 2 * h ^ 48
    - (15 : F[X]) * a1 * a2 * a5 * h ^ 42
    - (60 : F[X]) * a1 * a3 * a4 * h ^ 42
    + (24 : F[X]) * a1 * a3 * b8 * h ^ 38
    + (45 : F[X]) * a1 * a4 ^ 2 * a5 * h ^ 36
    + (15 : F[X]) * a1 * a4 * a5 ^ 3 * h ^ 30
    - (48 : F[X]) * a1 * a4 * a5 * b8 * h ^ 32
    + (21 : F[X]) * a1 * a4 * b7 * h ^ 38
    - (15 : F[X]) * a1 * a5 ^ 5 * h ^ 24
    + (24 : F[X]) * a1 * a5 ^ 3 * b8 * h ^ 26
    - (21 : F[X]) * a1 * a5 ^ 2 * b7 * h ^ 32
    + (18 : F[X]) * a1 * a5 * b6 * h ^ 38
    - (15 : F[X]) * a1 * b5 * h ^ 44
    - (30 : F[X]) * a2 ^ 2 * a4 * h ^ 42
    + (12 : F[X]) * a2 ^ 2 * b8 * h ^ 38
    - (30 : F[X]) * a2 * a3 ^ 2 * h ^ 42
    + (90 : F[X]) * a2 * a3 * a4 * a5 * h ^ 36
    + (15 : F[X]) * a2 * a3 * a5 ^ 3 * h ^ 30
    - (48 : F[X]) * a2 * a3 * a5 * b8 * h ^ 32
    + (21 : F[X]) * a2 * a3 * b7 * h ^ 38
    + (30 : F[X]) * a2 * a4 ^ 3 * h ^ 36
    - (45 : F[X]) * a2 * a4 ^ 2 * a5 ^ 2 * h ^ 30
    - (24 : F[X]) * a2 * a4 ^ 2 * b8 * h ^ 32
    - (30 : F[X]) * a2 * a4 * a5 ^ 4 * h ^ 24
    + (72 : F[X]) * a2 * a4 * a5 ^ 2 * b8 * h ^ 26
    - (42 : F[X]) * a2 * a4 * a5 * b7 * h ^ 32
    + (18 : F[X]) * a2 * a4 * b6 * h ^ 38
    + (15 : F[X]) * a2 * a5 ^ 6 * h ^ 18
    - (24 : F[X]) * a2 * a5 ^ 4 * b8 * h ^ 20
    + (21 : F[X]) * a2 * a5 ^ 3 * b7 * h ^ 26
    - (18 : F[X]) * a2 * a5 ^ 2 * b6 * h ^ 32
    + (15 : F[X]) * a2 * a5 * b5 * h ^ 38
    - (12 : F[X]) * a2 * b4 * h ^ 44
    + (15 : F[X]) * a3 ^ 3 * a5 * h ^ 36
    + (45 : F[X]) * a3 ^ 2 * a4 ^ 2 * h ^ 36
    - (45 : F[X]) * a3 ^ 2 * a4 * a5 ^ 2 * h ^ 30
    - (24 : F[X]) * a3 ^ 2 * a4 * b8 * h ^ 32
    - (15 : F[X]) * a3 ^ 2 * a5 ^ 4 * h ^ 24
    + (36 : F[X]) * a3 ^ 2 * a5 ^ 2 * b8 * h ^ 26
    - (21 : F[X]) * a3 ^ 2 * a5 * b7 * h ^ 32
    + (9 : F[X]) * a3 ^ 2 * b6 * h ^ 38
    - (75 : F[X]) * a3 * a4 ^ 3 * a5 * h ^ 30
    + (30 : F[X]) * a3 * a4 ^ 2 * a5 ^ 3 * h ^ 24
    + (72 : F[X]) * a3 * a4 ^ 2 * a5 * b8 * h ^ 26
    - (21 : F[X]) * a3 * a4 ^ 2 * b7 * h ^ 32
    + (45 : F[X]) * a3 * a4 * a5 ^ 5 * h ^ 18
    - (96 : F[X]) * a3 * a4 * a5 ^ 3 * b8 * h ^ 20
    + (63 : F[X]) * a3 * a4 * a5 ^ 2 * b7 * h ^ 26
    - (36 : F[X]) * a3 * a4 * a5 * b6 * h ^ 32
    + (15 : F[X]) * a3 * a4 * b5 * h ^ 38
    - (15 : F[X]) * a3 * a5 ^ 7 * h ^ 12
    + (24 : F[X]) * a3 * a5 ^ 5 * b8 * h ^ 14
    - (21 : F[X]) * a3 * a5 ^ 4 * b7 * h ^ 20
    + (18 : F[X]) * a3 * a5 ^ 3 * b6 * h ^ 26
    - (15 : F[X]) * a3 * a5 ^ 2 * b5 * h ^ 32
    + (12 : F[X]) * a3 * a5 * b4 * h ^ 38
    - (9 : F[X]) * a3 * b3 * h ^ 44
    - (6 : F[X]) * a4 ^ 5 * h ^ 30
    + (30 : F[X]) * a4 ^ 4 * a5 ^ 2 * h ^ 24
    + (6 : F[X]) * a4 ^ 4 * b8 * h ^ 26
    - (48 : F[X]) * a4 ^ 3 * a5 ^ 2 * b8 * h ^ 20
    + (21 : F[X]) * a4 ^ 3 * a5 * b7 * h ^ 26
    - (6 : F[X]) * a4 ^ 3 * b6 * h ^ 32
    - (30 : F[X]) * a4 ^ 2 * a5 ^ 6 * h ^ 12
    + (60 : F[X]) * a4 ^ 2 * a5 ^ 4 * b8 * h ^ 14
    - (42 : F[X]) * a4 ^ 2 * a5 ^ 3 * b7 * h ^ 20
    + (27 : F[X]) * a4 ^ 2 * a5 ^ 2 * b6 * h ^ 26
    - (15 : F[X]) * a4 ^ 2 * a5 * b5 * h ^ 32
    + (6 : F[X]) * a4 ^ 2 * b4 * h ^ 38
    + (15 : F[X]) * a4 * a5 ^ 8 * h ^ 6
    - (24 : F[X]) * a4 * a5 ^ 6 * b8 * h ^ 8
    + (21 : F[X]) * a4 * a5 ^ 5 * b7 * h ^ 14
    - (18 : F[X]) * a4 * a5 ^ 4 * b6 * h ^ 20
    + (15 : F[X]) * a4 * a5 ^ 3 * b5 * h ^ 26
    - (12 : F[X]) * a4 * a5 ^ 2 * b4 * h ^ 32
    + (9 : F[X]) * a4 * a5 * b3 * h ^ 38
    - (6 : F[X]) * a4 * b2 * h ^ 44
    - (2 : F[X]) * a5 ^ 10
    + (3 : F[X]) * a5 ^ 8 * b8 * h ^ 2
    - (3 : F[X]) * a5 ^ 7 * b7 * h ^ 8
    + (3 : F[X]) * a5 ^ 6 * b6 * h ^ 14
    - (3 : F[X]) * a5 ^ 5 * b5 * h ^ 20
    + (3 : F[X]) * a5 ^ 4 * b4 * h ^ 26
    - (3 : F[X]) * a5 ^ 3 * b3 * h ^ 32
    + (3 : F[X]) * a5 ^ 2 * b2 * h ^ 38
    - (3 : F[X]) * a5 * b1 * h ^ 44
    + (18 : F[X]) * b0 * h ^ 50 := by
  simp [localClearedTenthDefect610, map_zero]

set_option maxHeartbeats 80000000 in
/-- Clearing the first integral
`X - γ E - (5/6) δ D - (2/3) ε C - (1/2) ζ B - (1/3) η A
- (10/9) C E - (5/9) D² + (5/27) A² E + (10/27) A B D + (5/27) A C²
+ (5/27) B² C - (10/81) A² B² - (20/243) A³ C + (7/729) A⁵
- (4/9) α A E - (4/9) α B D - (2/9) α C² + (4/27) α A² C
+ (4/27) α A B² - (5/243) α A⁴ - (7/36) β A D - (7/36) β B C
+ (35/432) β A² B + (5/36) δ A B + (1/9) ε A²
- (3/4) L B E - (3/4) L C D + (3/8) L A B C + (3/16) L A² D
+ (1/16) L B³ - (3/32) L A³ B`
against `h⁵⁰` on the ninth-power face. -/
theorem tenthDefect_eq_clearedIota610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (18 : F) * h ^ 50 *
        iotaResidual610
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
          (depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3)
          (depressedV610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3 b2)
          (depressedX610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1 b0) =
    (30 : F) * a0 * a2 * h ^ 48
    - (15 : F) * a0 * a3 * a5 * h ^ 42
    - (9 : F) * a0 * a3 * h ^ 47 * lambda
    - (30 : F) * a0 * a4 ^ 2 * h ^ 42
    + (18 : F) * a0 * a4 * a5 * h ^ 41 * lambda
    + (24 : F) * a0 * a4 * b8 * h ^ 38
    + (15 : F) * a0 * a5 ^ 4 * h ^ 30
    - (9 : F) * a0 * a5 ^ 3 * h ^ 35 * lambda
    - (24 : F) * a0 * a5 ^ 2 * b8 * h ^ 32
    + (21 : F) * a0 * a5 * b7 * h ^ 38
    - (18 : F) * a0 * b6 * h ^ 44
    + (15 : F) * a1 ^ 2 * h ^ 48
    - (15 : F) * a1 * a2 * a5 * h ^ 42
    - (9 : F) * a1 * a2 * h ^ 47 * lambda
    - (60 : F) * a1 * a3 * a4 * h ^ 42
    + (18 : F) * a1 * a3 * a5 * h ^ 41 * lambda
    + (24 : F) * a1 * a3 * b8 * h ^ 38
    + (45 : F) * a1 * a4 ^ 2 * a5 * h ^ 36
    + (9 : F) * a1 * a4 ^ 2 * h ^ 41 * lambda
    + (15 : F) * a1 * a4 * a5 ^ 3 * h ^ 30
    - (27 : F) * a1 * a4 * a5 ^ 2 * h ^ 35 * lambda
    - (48 : F) * a1 * a4 * a5 * b8 * h ^ 32
    + (21 : F) * a1 * a4 * b7 * h ^ 38
    - (15 : F) * a1 * a5 ^ 5 * h ^ 24
    + (9 : F) * a1 * a5 ^ 4 * h ^ 29 * lambda
    + (24 : F) * a1 * a5 ^ 3 * b8 * h ^ 26
    - (21 : F) * a1 * a5 ^ 2 * b7 * h ^ 32
    + (18 : F) * a1 * a5 * b6 * h ^ 38
    - (15 : F) * a1 * b5 * h ^ 44
    - (30 : F) * a2 ^ 2 * a4 * h ^ 42
    + (9 : F) * a2 ^ 2 * a5 * h ^ 41 * lambda
    + (12 : F) * a2 ^ 2 * b8 * h ^ 38
    - (30 : F) * a2 * a3 ^ 2 * h ^ 42
    + (90 : F) * a2 * a3 * a4 * a5 * h ^ 36
    + (18 : F) * a2 * a3 * a4 * h ^ 41 * lambda
    + (15 : F) * a2 * a3 * a5 ^ 3 * h ^ 30
    - (27 : F) * a2 * a3 * a5 ^ 2 * h ^ 35 * lambda
    - (48 : F) * a2 * a3 * a5 * b8 * h ^ 32
    + (21 : F) * a2 * a3 * b7 * h ^ 38
    + (30 : F) * a2 * a4 ^ 3 * h ^ 36
    - (45 : F) * a2 * a4 ^ 2 * a5 ^ 2 * h ^ 30
    - (27 : F) * a2 * a4 ^ 2 * a5 * h ^ 35 * lambda
    - (24 : F) * a2 * a4 ^ 2 * b8 * h ^ 32
    - (30 : F) * a2 * a4 * a5 ^ 4 * h ^ 24
    + (36 : F) * a2 * a4 * a5 ^ 3 * h ^ 29 * lambda
    + (72 : F) * a2 * a4 * a5 ^ 2 * b8 * h ^ 26
    - (42 : F) * a2 * a4 * a5 * b7 * h ^ 32
    + (18 : F) * a2 * a4 * b6 * h ^ 38
    + (15 : F) * a2 * a5 ^ 6 * h ^ 18
    - (9 : F) * a2 * a5 ^ 5 * h ^ 23 * lambda
    - (24 : F) * a2 * a5 ^ 4 * b8 * h ^ 20
    + (21 : F) * a2 * a5 ^ 3 * b7 * h ^ 26
    - (18 : F) * a2 * a5 ^ 2 * b6 * h ^ 32
    + (15 : F) * a2 * a5 * b5 * h ^ 38
    - (12 : F) * a2 * b4 * h ^ 44
    + (15 : F) * a3 ^ 3 * a5 * h ^ 36
    + (3 : F) * a3 ^ 3 * h ^ 41 * lambda
    + (45 : F) * a3 ^ 2 * a4 ^ 2 * h ^ 36
    - (45 : F) * a3 ^ 2 * a4 * a5 ^ 2 * h ^ 30
    - (27 : F) * a3 ^ 2 * a4 * a5 * h ^ 35 * lambda
    - (24 : F) * a3 ^ 2 * a4 * b8 * h ^ 32
    - (15 : F) * a3 ^ 2 * a5 ^ 4 * h ^ 24
    + (18 : F) * a3 ^ 2 * a5 ^ 3 * h ^ 29 * lambda
    + (36 : F) * a3 ^ 2 * a5 ^ 2 * b8 * h ^ 26
    - (21 : F) * a3 ^ 2 * a5 * b7 * h ^ 32
    + (9 : F) * a3 ^ 2 * b6 * h ^ 38
    - (75 : F) * a3 * a4 ^ 3 * a5 * h ^ 30
    - (9 : F) * a3 * a4 ^ 3 * h ^ 35 * lambda
    + (30 : F) * a3 * a4 ^ 2 * a5 ^ 3 * h ^ 24
    + (54 : F) * a3 * a4 ^ 2 * a5 ^ 2 * h ^ 29 * lambda
    + (72 : F) * a3 * a4 ^ 2 * a5 * b8 * h ^ 26
    - (21 : F) * a3 * a4 ^ 2 * b7 * h ^ 32
    + (45 : F) * a3 * a4 * a5 ^ 5 * h ^ 18
    - (45 : F) * a3 * a4 * a5 ^ 4 * h ^ 23 * lambda
    - (96 : F) * a3 * a4 * a5 ^ 3 * b8 * h ^ 20
    + (63 : F) * a3 * a4 * a5 ^ 2 * b7 * h ^ 26
    - (36 : F) * a3 * a4 * a5 * b6 * h ^ 32
    + (15 : F) * a3 * a4 * b5 * h ^ 38
    - (15 : F) * a3 * a5 ^ 7 * h ^ 12
    + (9 : F) * a3 * a5 ^ 6 * h ^ 17 * lambda
    + (24 : F) * a3 * a5 ^ 5 * b8 * h ^ 14
    - (21 : F) * a3 * a5 ^ 4 * b7 * h ^ 20
    + (18 : F) * a3 * a5 ^ 3 * b6 * h ^ 26
    - (15 : F) * a3 * a5 ^ 2 * b5 * h ^ 32
    + (12 : F) * a3 * a5 * b4 * h ^ 38
    - (9 : F) * a3 * b3 * h ^ 44
    - (6 : F) * a4 ^ 5 * h ^ 30
    + (30 : F) * a4 ^ 4 * a5 ^ 2 * h ^ 24
    + (9 : F) * a4 ^ 4 * a5 * h ^ 29 * lambda
    + (6 : F) * a4 ^ 4 * b8 * h ^ 26
    - (30 : F) * a4 ^ 3 * a5 ^ 3 * h ^ 23 * lambda
    - (48 : F) * a4 ^ 3 * a5 ^ 2 * b8 * h ^ 20
    + (21 : F) * a4 ^ 3 * a5 * b7 * h ^ 26
    - (6 : F) * a4 ^ 3 * b6 * h ^ 32
    - (30 : F) * a4 ^ 2 * a5 ^ 6 * h ^ 12
    + (27 : F) * a4 ^ 2 * a5 ^ 5 * h ^ 17 * lambda
    + (60 : F) * a4 ^ 2 * a5 ^ 4 * b8 * h ^ 14
    - (42 : F) * a4 ^ 2 * a5 ^ 3 * b7 * h ^ 20
    + (27 : F) * a4 ^ 2 * a5 ^ 2 * b6 * h ^ 26
    - (15 : F) * a4 ^ 2 * a5 * b5 * h ^ 32
    + (6 : F) * a4 ^ 2 * b4 * h ^ 38
    + (15 : F) * a4 * a5 ^ 8 * h ^ 6
    - (9 : F) * a4 * a5 ^ 7 * h ^ 11 * lambda
    - (24 : F) * a4 * a5 ^ 6 * b8 * h ^ 8
    + (21 : F) * a4 * a5 ^ 5 * b7 * h ^ 14
    - (18 : F) * a4 * a5 ^ 4 * b6 * h ^ 20
    + (15 : F) * a4 * a5 ^ 3 * b5 * h ^ 26
    - (12 : F) * a4 * a5 ^ 2 * b4 * h ^ 32
    + (9 : F) * a4 * a5 * b3 * h ^ 38
    - (6 : F) * a4 * b2 * h ^ 44
    - (2 : F) * a5 ^ 10
    + (1 : F) * a5 ^ 9 * h ^ 5 * lambda
    + (3 : F) * a5 ^ 8 * b8 * h ^ 2
    - (3 : F) * a5 ^ 7 * b7 * h ^ 8
    + (3 : F) * a5 ^ 6 * b6 * h ^ 14
    - (3 : F) * a5 ^ 5 * b5 * h ^ 20
    + (3 : F) * a5 ^ 4 * b4 * h ^ 26
    - (3 : F) * a5 ^ 3 * b3 * h ^ 32
    + (3 : F) * a5 ^ 2 * b2 * h ^ 38
    - (3 : F) * a5 * b1 * h ^ 44
    + (18 : F) * b0 * h ^ 50 := by
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
  have h32 : (32 : F) ≠ 0 := by norm_num
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
  have h729 : (729 : F) ≠ 0 := by norm_num
  have h7776 : (7776 : F) ≠ 0 := by norm_num
  have h11664 : (11664 : F) ≠ 0 := by norm_num
  have h46656 : (46656 : F) ≠ 0 := by norm_num
  have h93312 : (93312 : F) ≠ 0 := by norm_num
  have h186624 : (186624 : F) ≠ 0 := by norm_num
  have h60466176 : (60466176 : F) ≠ 0 := by norm_num
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hh25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
  have hh30 : h ^ 30 ≠ 0 := pow_ne_zero 30 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh40 : h ^ 40 ≠ 0 := pow_ne_zero 40 hh
  have hh45 : h ^ 45 ≠ 0 := pow_ne_zero 45 hh
  have hh50 : h ^ 50 ≠ 0 := pow_ne_zero 50 hh
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
  have hU :
      depressedU610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 =
        (30 * a5 ^ 7 - 7 * lambda * a5 ^ 6 * h ^ 5 -
            84 * a5 ^ 5 * b8 * h ^ 2 + 315 * a5 ^ 4 * b7 * h ^ 8 -
            1080 * a5 ^ 3 * b6 * h ^ 14 + 3240 * a5 ^ 2 * b5 * h ^ 20 -
            7776 * a5 * b4 * h ^ 26 + 11664 * b3 * h ^ 32) /
          (11664 * h ^ 35) :=
    depressedU610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 lambda hh hN
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
  have hX :
      depressedX610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 b2 b1 b0 =
        (-9 * a5 ^ 10 + 2 * lambda * a5 ^ 9 * h ^ 5 +
            36 * a5 ^ 8 * b8 * h ^ 2 - 216 * a5 ^ 7 * b7 * h ^ 8 +
            1296 * a5 ^ 6 * b6 * h ^ 14 - 7776 * a5 ^ 5 * b5 * h ^ 20 +
            46656 * a5 ^ 4 * b4 * h ^ 26 - 279936 * a5 ^ 3 * b3 * h ^ 32 +
            1679616 * a5 ^ 2 * b2 * h ^ 38 - 10077696 * a5 * b1 * h ^ 44 +
            60466176 * b0 * h ^ 50) /
          (60466176 * h ^ 50) :=
    depressedX610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 lambda
      hh hN
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
  simp only [iotaResidual610, hL, hA, hB, hC, hD0, hE0, hP, hQ, hR, hS,
    hT, hU, hV, hX, alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610]
  field_simp [hh, h2, h3, h4, h5, h6, h8, h9, h12, h16, h18, h27, h32,
    h36, h54, h72, h81, h144, h216, h243, h324, h432, h648, h729, h7776,
    h11664, h46656, h93312, h186624, h60466176, hh10, hh15, hh20, hh25,
    hh30, hh35, hh40, hh45, hh50]
  ring

end Depression610Tenth

/-! ## Degree-`5` depressed Jacobian coefficient -/

section DepressedRow610Tenth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]

/-- For a depressed monic sextic and a monic decic whose `z⁹` coefficient is
already a differential constant, the degree-`5` Jacobian coefficient is
exactly `6 R E' + 5 S D' + 4 T C' + 3 U B' + 2 V A' - D S' - 2 C T'
- 3 B U' - 4 A V' - 6 X'`. -/
theorem differentialJacobian_coeff_5_monicSexticDecic
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 6 < n → f.coeff n = 0) (hf6 : f.coeff 6 = 1)
    (hf5 : f.coeff 5 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 5 =
      (6 : F) * g.coeff 6 * d (f.coeff 0) +
        (5 : F) * g.coeff 5 * d (f.coeff 1) +
        (4 : F) * g.coeff 4 * d (f.coeff 2) +
        (3 : F) * g.coeff 3 * d (f.coeff 3) +
        (2 : F) * g.coeff 2 * d (f.coeff 4) -
          (1 : F) * f.coeff 1 * d (g.coeff 5) -
          (2 : F) * f.coeff 2 * d (g.coeff 4) -
          (3 : F) * f.coeff 3 * d (g.coeff 3) -
          (4 : F) * f.coeff 4 * d (g.coeff 2) -
          (6 : F) * d (g.coeff 0) := by
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
  have hmem08 : ((0, 5) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem17 : ((1, 4) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem26 : ((2, 3) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem35 : ((3, 2) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem44 : ((4, 1) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hmem53 : ((5, 0) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ) :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (by norm_num)
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 5 =
        (6 : F) * g.coeff 6 * d (f.coeff 0) +
          (5 : F) * g.coeff 5 * d (f.coeff 1) +
          (4 : F) * g.coeff 4 * d (f.coeff 2) +
          (3 : F) * g.coeff 3 * d (f.coeff 3) +
          (2 : F) * g.coeff 2 * d (f.coeff 4) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 5) : ℕ × ℕ) ≠ (1, 4) := by decide
    have hne08_26 : ((0, 5) : ℕ × ℕ) ≠ (2, 3) := by decide
    have hne08_35 : ((0, 5) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne08_44 : ((0, 5) : ℕ × ℕ) ≠ (4, 1) := by decide
    have hne17_26 : ((1, 4) : ℕ × ℕ) ≠ (2, 3) := by decide
    have hne17_35 : ((1, 4) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne17_44 : ((1, 4) : ℕ × ℕ) ≠ (4, 1) := by decide
    have hne26_35 : ((2, 3) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne26_44 : ((2, 3) : ℕ × ℕ) ≠ (4, 1) := by decide
    have hne35_44 : ((3, 2) : ℕ × ℕ) ≠ (4, 1) := by decide
    have hsubset :
        ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1)} : Finset (ℕ × ℕ)) ⊆
          Finset.HasAntidiagonal.antidiagonal (5 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem08
      · subst b; exact hmem17
      · subst b; exact hmem26
      · subst b; exact hmem35
      · subst b; exact hmem44
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (∑ p ∈ ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 *
              g.derivative.coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 5 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 5) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne44 : b ≠ (4, 1) := by
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
        (∑ p ∈ ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 5 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 4 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 3 +
            (coefficientDeriv d f).coeff 3 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 4 * g.derivative.coeff 1 := by
      rw [Finset.sum_insert (by simp [hne08_17, hne08_26, hne08_35, hne08_44]),
        Finset.sum_insert (by simp [hne17_26, hne17_35, hne17_44]),
        Finset.sum_insert (by simp [hne26_35, hne26_44]),
        Finset.sum_insert (by simp [hne35_44]), Finset.sum_singleton]
      ring
    have hder5g : g.derivative.coeff 5 = (6 : F) * g.coeff 6 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder4g : g.derivative.coeff 4 = (5 : F) * g.coeff 5 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder3g : g.derivative.coeff 3 = (4 : F) * g.coeff 4 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder2g : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]
      ring
    have hder1g : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]
      ring
    rw [hsum, hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder5g, hder4g, hder3g, hder2g, hder1g]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 5 =
        (1 : F) * f.coeff 1 * d (g.coeff 5) +
          (2 : F) * f.coeff 2 * d (g.coeff 4) +
          (3 : F) * f.coeff 3 * d (g.coeff 3) +
          (4 : F) * f.coeff 4 * d (g.coeff 2) +
          (6 : F) * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul]
    have hne08_17 : ((0, 5) : ℕ × ℕ) ≠ (1, 4) := by decide
    have hne08_26 : ((0, 5) : ℕ × ℕ) ≠ (2, 3) := by decide
    have hne08_35 : ((0, 5) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne08_53 : ((0, 5) : ℕ × ℕ) ≠ (5, 0) := by decide
    have hne17_26 : ((1, 4) : ℕ × ℕ) ≠ (2, 3) := by decide
    have hne17_35 : ((1, 4) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne17_53 : ((1, 4) : ℕ × ℕ) ≠ (5, 0) := by decide
    have hne26_35 : ((2, 3) : ℕ × ℕ) ≠ (3, 2) := by decide
    have hne26_53 : ((2, 3) : ℕ × ℕ) ≠ (5, 0) := by decide
    have hne35_53 : ((3, 2) : ℕ × ℕ) ≠ (5, 0) := by decide
    have hsubset : ({(0, 5), (1, 4), (2, 3), (3, 2), (5, 0)} : Finset (ℕ × ℕ)) ⊆
        Finset.HasAntidiagonal.antidiagonal (5 : ℕ) := by
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hb | hb | hb | hb | hb
      · subst b; exact hmem08
      · subst b; exact hmem17
      · subst b; exact hmem26
      · subst b; exact hmem35
      · subst b; exact hmem53
    have hsum :
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (5 : ℕ),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          (∑ p ∈ ({(0, 5), (1, 4), (2, 3), (3, 2), (5, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 *
              (coefficientDeriv d g).coeff p.2) := by
      refine (Finset.sum_subset hsubset ?_).symm
      intro b hb hbnot
      have hij : b.1 + b.2 = 5 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have hne08 : b ≠ (0, 5) := by
        intro hEq; subst b; exact hbnot (Finset.mem_insert_self _ _)
      have hne17 : b ≠ (1, 4) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne26 : b ≠ (2, 3) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne35 : b ≠ (3, 2) := by
        intro hEq; subst b; exact hbnot (by simp)
      have hne53 : b ≠ (5, 0) := by
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
        (∑ p ∈ ({(0, 5), (1, 4), (2, 3), (3, 2), (5, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 5 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 4 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 3 +
            f.derivative.coeff 3 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 5 * (coefficientDeriv d g).coeff 0 := by
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


set_option maxHeartbeats 80000000 in
theorem iotaResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R S0 T0 U0 V0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hgamma : d (gammaResidual610 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual610 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual610 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual610 L A B C0 D0 E0 P Q R S0 U0) = 0)
    (heta : d (etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0) = 0)
    (hrow : (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A - (1 : F) * D0 * d S0 -
        (2 : F) * C0 * d T0 - (3 : F) * B * d U0 -
        (4 : F) * A * d V0 - (6 : F) * d X0 = 0) :
    d (iotaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 X0) = 0 := by
  have h2 : d (2 : F) = 0 := d.map_natCast 2
  have h3 : d (3 : F) = 0 := d.map_natCast 3
  have h4 : d (4 : F) = 0 := d.map_natCast 4
  have h5 : d (5 : F) = 0 := d.map_natCast 5
  have h6 : d (6 : F) = 0 := d.map_natCast 6
  have h7 : d (7 : F) = 0 := d.map_natCast 7
  have h8 : d (8 : F) = 0 := d.map_natCast 8
  have h9 : d (9 : F) = 0 := d.map_natCast 9
  have h16 : d (16 : F) = 0 := d.map_natCast 16
  have h27 : d (27 : F) = 0 := d.map_natCast 27
  have h36 : d (36 : F) = 0 := d.map_natCast 36
  have h72 : d (72 : F) = 0 := d.map_natCast 72
  have h81 : d (81 : F) = 0 := d.map_natCast 81
  have h128 : d (128 : F) = 0 := d.map_natCast 128
  have h243 : d (243 : F) = 0 := d.map_natCast 243
  have h1296 : d (1296 : F) = 0 := d.map_natCast 1296
  have h53 : d (5 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h5]
  have h32 : d (3 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h3]
  have h43 : d (4 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h4]
  have h76 : d (7 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h7]
  have h56c : d (5 / 6 : F) = 0 := by
    simp [Derivation.leibniz_div, h6, h5]
  have h23 : d (2 / 3 : F) = 0 := by
    simp [Derivation.leibniz_div, h3, h2]
  have h12 : d (1 / 2 : F) = 0 := by
    simp [Derivation.leibniz_inv, h2]
  have h109 : d (10 / 9 : F) = 0 := by
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    simp [Derivation.leibniz_div, h9, h10]
  have h49 : d (4 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h4]
  have h772 : d (7 / 72 : F) = 0 := by
    simp [Derivation.leibniz_div, h72, h7]
  have h581 : d (5 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h5]
  have h736 : d (7 / 36 : F) = 0 := by
    simp [Derivation.leibniz_div, h36, h7]
  have h1027 : d (10 / 27 : F) = 0 := by
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    simp [Derivation.leibniz_div, h27, h10]
  have h572 : d (5 / 72 : F) = 0 := by
    simp [Derivation.leibniz_div, h72, h5]
  have h527 : d (5 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h5]
  have h427 : d (4 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h4]
  have h351296 : d (35 / 1296 : F) = 0 := by
    have h35 : d (35 : F) = 0 := d.map_natCast 35
    simp [Derivation.leibniz_div, h1296, h35]
  have h20243 : d (20 / 243 : F) = 0 := by
    have h20 : d (20 : F) = 0 := d.map_natCast 20
    simp [Derivation.leibniz_div, h243, h20]
  have h38 : d (3 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h3]
  have h34 : d (3 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h3]
  have h316 : d (3 / 16 : F) = 0 := by
    simp [Derivation.leibniz_div, h16, h3]
  have h3128 : d (3 / 128 : F) = 0 := by
    simp [Derivation.leibniz_div, h128, h3]
  have hsq : d (A * A) = (2 : F) * A * d A := by
    simp [Derivation.leibniz]
    ring
  have hsqB : d (B * B) = (2 : F) * B * d B := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hsqC : d (C0 * C0) = (2 : F) * C0 * d C0 := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hcub : d (A ^ 3) = (3 : F) * A ^ 2 * d A := by
    have h2A : d (A ^ 2) = (2 : F) * A * d A := by
      simpa [pow_two] using hsq
    simp [pow_three, Derivation.leibniz, h2A]
    ring
  have hcubB : d (B ^ 3) = (3 : F) * B ^ 2 * d B := by
    have h2B : d (B ^ 2) = (2 : F) * B * d B := by
      simpa [pow_two] using hsqB
    simp [pow_three, Derivation.leibniz, h2B]
    ring
  have hquar : d (A ^ 4) = (4 : F) * A ^ 3 * d A := by
    have : A ^ 4 = A ^ 3 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hcub]
    ring
  have hPderiv : d P = (5 / 3 : F) * d A := by
    have halpha' : d P - (5 / 3 : F) * d A = 0 := by
      simpa [alphaResidual610, map_sub, Derivation.leibniz, h53, zero_mul,
        add_zero] using halpha
    linear_combination halpha'
  have hQderiv : d Q = (5 / 3 : F) * d B + (3 / 2 : F) * L * d A := by
    have hbeta' :
        d Q - (5 / 3 : F) * d B - (3 / 2 : F) * L * d A = 0 := by
      simpa [betaResidual610, map_sub, Derivation.leibniz, h53, h32, hL,
        zero_mul, add_zero, mul_zero] using hbeta
    linear_combination hbeta'
  have hRderiv : d R = (5 / 3 : F) * d C0 + (3 / 2 : F) * L * d B +
      (4 / 3 : F) * P * d A - (10 / 9 : F) * A * d A := by
    have hgamma' :
        d R - (5 / 3 : F) * d C0 - (3 / 2 : F) * L * d B -
          ((4 / 3 : F) * P * d A + A * ((4 / 3 : F) * d P)) +
          (5 / 3 : F) * (A * d A + A * d A) = 0 := by
      simpa [gammaResidual610, map_sub, map_add, Derivation.leibniz, h53,
        h32, h43, hL, zero_mul, add_zero, mul_zero, pow_two] using hgamma
    linear_combination hgamma' + (-(4 / 3 : F) * A) * hPderiv.symm
  have hSderiv : d S0 = (5 / 3 : F) * d D0 + (3 / 2 : F) * L * d C0 +
      (4 / 3 : F) * P * d B - (10 / 9 : F) * A * d B +
      (7 / 6 : F) * Q * d A - (A * L + (5 / 6 : F) * B) * d A := by
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
    have h18 : d (18 : F) = 0 := d.map_natCast 18
    have h55 : d (55 : F) = 0 := d.map_natCast 55
    have h11 : d (11 : F) = 0 := d.map_natCast 11
    have h5518 : d (55 / 18 : F) = 0 := by
      simp [Derivation.leibniz_div, h18, h55]
    have h118 : d (11 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h11]
    simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
      h5518, h118, zero_mul, add_zero, mul_zero, hsq] at hdlt
    rw [hPderiv, hQderiv] at hdlt
    linear_combination hdlt
  have hTderiv : d T0 = (5 / 3 : F) * d E0 + (3 / 2 : F) * L * d D0 +
      (4 / 3 : F) * P * d C0 - (10 / 9 : F) * A * d C0 +
      (7 / 6 : F) * Q * d B - (A * L + (5 / 6 : F) * B) * d B +
      R * d A +
      ((20 / 27 : F) * A ^ 2 - (8 / 9 : F) * A * P - (3 / 4 : F) * L * B -
        (5 / 9 : F) * C0) * d A := by
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
    have h18 : d (18 : F) = 0 := d.map_natCast 18
    have h25 : d (25 : F) = 0 := d.map_natCast 25
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    have h100 : d (100 : F) = 0 := d.map_natCast 100
    have h259 : d (25 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h25]
    have h2518 : d (25 / 18 : F) = 0 := by
      simp [Derivation.leibniz_div, h18, h25]
    have h52 : d (5 / 2 : F) = 0 := by
      simp [Derivation.leibniz_div, h2, h5]
    have h10081 : d (100 / 81 : F) = 0 := by
      simp [Derivation.leibniz_div, h81, h100]
    have hcub' : d (A * A * A) = (3 : F) * (A * A) * d A := by
      simp [Derivation.leibniz]
      ring
    simp [map_sub, map_add, Derivation.leibniz, h53, h32, h43, h76, hL,
      h259, h2518, h52, h109, h10081, zero_mul, add_zero, mul_zero, hsq,
      hcub', hsqB] at heps
    rw [hPderiv, hQderiv, hRderiv] at heps
    linear_combination heps
  have hUderiv : d U0 =
      (3 / 2 : F) * L * d E0 +
        (4 / 3 : F) * P * d D0 + (4 / 3 : F) * D0 * d P +
        (7 / 6 : F) * Q * d C0 + (7 / 6 : F) * C0 * d Q +
        R * d B + B * d R +
        (5 / 6 : F) * S0 * d A + (5 / 6 : F) * A * d S0 -
        (5 / 2 : F) * A * d D0 - (5 / 2 : F) * D0 * d A -
        (5 / 2 : F) * B * d C0 - (5 / 2 : F) * C0 * d B -
        (2 : F) * A * B * d P - (2 : F) * A * P * d B -
        (2 : F) * B * P * d A -
        (7 / 8 : F) * (A * A) * d Q - (7 / 4 : F) * Q * A * d A -
        (9 / 4 : F) * L * A * d C0 - (9 / 4 : F) * L * C0 * d A -
        (9 / 4 : F) * L * B * d B +
        (25 / 8 : F) * (A * A) * d B + (25 / 4 : F) * A * B * d A +
        (45 / 16 : F) * L * (A * A) * d A := by
    have hexp :
        zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 =
          U0 - (3 / 2 : F) * L * E0 - (4 / 3 : F) * P * D0 -
            (7 / 6 : F) * Q * C0 - R * B - (5 / 6 : F) * S0 * A +
            (5 / 2 : F) * A * D0 + (5 / 2 : F) * B * C0 +
            (2 : F) * A * B * P + (7 / 8 : F) * Q * (A * A) +
            (9 / 4 : F) * L * A * C0 + (9 / 8 : F) * L * (B * B) -
            (25 / 8 : F) * (A * A) * B -
            (15 / 16 : F) * L * (A * A * A) := by
      simp only [zetaResidual610, alphaResidual610, betaResidual610,
        gammaResidual610, deltaResidual610, pow_two, pow_three]
      ring
    have hz := hzeta
    rw [hexp] at hz
    have h25 : d (25 : F) = 0 := d.map_natCast 25
    have h15 : d (15 : F) = 0 := d.map_natCast 15
    have h52 : d (5 / 2 : F) = 0 := by
      simp [Derivation.leibniz_div, h2, h5]
    have h78 : d (7 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h7]
    have h94 : d (9 / 4 : F) = 0 := by
      simp [Derivation.leibniz_div, h4, h9]
    have h98 : d (9 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h9]
    have h258 : d (25 / 8 : F) = 0 := by
      simp [Derivation.leibniz_div, h8, h25]
    have h16ne : (16 : F) ≠ 0 := by norm_num
    have h16inv : d (16 : F)⁻¹ = 0 := by
      have hone : (16 : F) * (16 : F)⁻¹ = 1 := mul_inv_cancel₀ h16ne
      have hd1 : d ((16 : F) * (16 : F)⁻¹) = 0 := by
        rw [hone]
        exact d.map_one_eq_zero
      have hleib :
          d ((16 : F) * (16 : F)⁻¹) =
            (16 : F) • d (16 : F)⁻¹ + (16 : F)⁻¹ • d (16 : F) :=
        Derivation.leibniz d (16 : F) (16 : F)⁻¹
      have hsum : (16 : F) * d (16 : F)⁻¹ + (16 : F)⁻¹ * d (16 : F) = 0 := by
        simpa [smul_eq_mul, hd1] using hleib.symm
      have honly : (16 : F) * d (16 : F)⁻¹ = 0 := by
        simpa [h16, mul_zero, add_zero] using hsum
      exact (mul_eq_zero.mp honly).resolve_left h16ne
    have h1516 : d (15 / 16 : F) = 0 := by
      simp [div_eq_mul_inv, Derivation.leibniz, h15, h16inv, zero_mul,
        add_zero, mul_zero]
    have hcub' : d (A * A * A) = (3 : F) * (A * A) * d A := by
      simp [Derivation.leibniz]
      ring
    simp [map_sub, map_add, Derivation.leibniz, h32, h43, h76, h56c, hL,
      h52, h78, h94, h98, h258, h1516, zero_mul, add_zero, mul_zero, hsq,
      hsqB, hcub', h2] at hz
    linear_combination hz
  have hVderiv : d V0 =
      (2 / 3 : F) * (d A * T0 + A * d T0) +
        (5 / 6 : F) * (d B * S0 + B * d S0) +
        (d C0 * R + C0 * d R) -
        (2 / 3 : F) * ((2 : F) * A * d A * R + (A * A) * d R) +
        (7 / 6 : F) * (d D0 * Q + D0 * d Q) -
        (14 / 9 : F) * (d A * B * Q + A * d B * Q + A * B * d Q) +
        (4 / 3 : F) * (d E0 * P + E0 * d P) -
        (16 / 9 : F) * (d A * C0 * P + A * d C0 * P + A * C0 * d P) -
        (8 / 9 : F) * ((2 : F) * B * d B * P + (B * B) * d P) +
        (56 / 81 : F) * ((3 : F) * (A * A) * d A * P +
          (A * A * A) * d P) -
        (20 / 9 : F) * (d A * E0 + A * d E0) -
        (20 / 9 : F) * (d B * D0 + B * d D0) -
        (10 / 9 : F) * ((2 : F) * C0 * d C0) -
        (2 : F) * L * (d A * D0 + A * d D0) -
        (2 : F) * L * (d B * C0 + B * d C0) +
        (7 / 3 : F) * L * ((2 : F) * A * d A * B + (A * A) * d B) +
        (70 / 27 : F) * ((2 : F) * A * d A * C0 + (A * A) * d C0) +
        (70 / 27 : F) * (d A * (B * B) + A * ((2 : F) * B * d B)) -
        (175 / 243 : F) * ((4 : F) * (A * A * A) * d A) := by
    have hexp :
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
    have h14 : d (14 : F) = 0 := d.map_natCast 14
    have h20 : d (20 : F) = 0 := d.map_natCast 20
    have h56 : d (56 : F) = 0 := d.map_natCast 56
    have h70 : d (70 : F) = 0 := d.map_natCast 70
    have h175 : d (175 : F) = 0 := d.map_natCast 175
    have h10 : d (10 : F) = 0 := d.map_natCast 10
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
    have h109' : d (10 / 9 : F) = 0 := by
      simp [Derivation.leibniz_div, h9, h10]
    have hcub' : d (A * A * A) = (3 : F) * (A * A) * d A := by
      simp [Derivation.leibniz]
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
      simp [Derivation.leibniz, smul_eq_mul, h5681, hcub']
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
      simp [Derivation.leibniz, smul_eq_mul, h109', hsqC]
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
    have he := heta
    rw [hexp] at he
    simp only [map_sub, map_add, hdAT, hdBS, hdCR, hdA2R, hdDQ, hdABQ,
      hdEP, hdACP, hdB2P, hdA3P, hdAE, hdBD, hdC2, hdADL, hdBCL, hdA2BL,
      hdA2C, hdAB2, hdA4] at he
    linear_combination he
  have hXderiv : d X0 = R * d E0 + (5 / 6 : F) * S0 * d D0 +
      (2 / 3 : F) * T0 * d C0 + (1 / 2 : F) * U0 * d B +
      (1 / 3 : F) * V0 * d A - (1 / 6 : F) * D0 * d S0 -
      (1 / 3 : F) * C0 * d T0 - (1 / 2 : F) * B * d U0 -
      (2 / 3 : F) * A * d V0 := by
    linear_combination (-1 / 6 : F) * hrow
  have h116 : d (1 / 16 : F) = 0 := by
    simp [Derivation.leibniz_inv, h16]
  have h29 : d (2 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h2]
  have h59 : d (5 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h5]
  have h89 : d (8 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h8]
  have h2027 : d (20 / 27 : F) = 0 := by
    have h20 : d (20 : F) = 0 := d.map_natCast 20
    simp [Derivation.leibniz_div, h27, h20]
  have h13 : d (1 / 3 : F) = 0 := by
    simp [Derivation.leibniz_inv, h3]
  have h19 : d (1 / 9 : F) = 0 := by
    simp [Derivation.leibniz_inv, h9]
  have h432 : d (432 : F) = 0 := d.map_natCast 432
  have h729 : d (729 : F) = 0 := d.map_natCast 729
  have h35432 : d (35 / 432 : F) = 0 := by
    have h35 : d (35 : F) = 0 := d.map_natCast 35
    simp [Derivation.leibniz_div, h432, h35]
  have h7729 : d (7 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729, h7]
  have h536 : d (5 / 36 : F) = 0 := by
    simp [Derivation.leibniz_div, h36, h5]
  have h1081 : d (10 / 81 : F) = 0 := by
    have h10 : d (10 : F) = 0 := d.map_natCast 10
    simp [Derivation.leibniz_div, h81, h10]
  have h5243 : d (5 / 243 : F) = 0 := by
    simp [Derivation.leibniz_div, h243, h5]
  have h481 : d (4 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h4]
  have h32n : d (32 : F) = 0 := d.map_natCast 32
  have h332 : d (3 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32n, h3]
  have h15 : d (15 : F) = 0 := d.map_natCast 15
  have h25 : d (25 : F) = 0 := d.map_natCast 25
  have h52 : d (5 / 2 : F) = 0 := by
    simp [Derivation.leibniz_div, h2, h5]
  have h78 : d (7 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h7]
  have h94 : d (9 / 4 : F) = 0 := by
    simp [Derivation.leibniz_div, h4, h9]
  have h98 : d (9 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h9]
  have h258 : d (25 / 8 : F) = 0 := by
    simp [Derivation.leibniz_div, h8, h25]
  have h16ne : (16 : F) ≠ 0 := by norm_num
  have h16inv : d (16 : F)⁻¹ = 0 := by
    have hone : (16 : F) * (16 : F)⁻¹ = 1 := mul_inv_cancel₀ h16ne
    have hd1 : d ((16 : F) * (16 : F)⁻¹) = 0 := by
      rw [hone]
      exact d.map_one_eq_zero
    have hleib :
        d ((16 : F) * (16 : F)⁻¹) =
          (16 : F) • d (16 : F)⁻¹ + (16 : F)⁻¹ • d (16 : F) :=
      Derivation.leibniz d (16 : F) (16 : F)⁻¹
    have hsum : (16 : F) * d (16 : F)⁻¹ + (16 : F)⁻¹ * d (16 : F) = 0 := by
      simpa [smul_eq_mul, hd1] using hleib.symm
    have honly : (16 : F) * d (16 : F)⁻¹ = 0 := by
      simpa [h16, mul_zero, add_zero] using hsum
    exact (mul_eq_zero.mp honly).resolve_left h16ne
  have h1516 : d (15 / 16 : F) = 0 := by
    simp [div_eq_mul_inv, Derivation.leibniz, h15, h16inv, zero_mul,
      add_zero, mul_zero]
  have hquint : d (A ^ 5) = (5 : F) * A ^ 4 * d A := by
    have : A ^ 5 = A ^ 4 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquar]
    ring
  have hsqD : d (D0 * D0) = (2 : F) * D0 * d D0 := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  simp only [iotaResidual610, map_sub, map_add, Derivation.leibniz,
    smul_eq_mul, h2, h3, h4, h5, h6, h7, h8, h9, h12, h13, h19, h23, h53,
    h32, h43, h76, h56c, h109, h49, h772, h581, h736, h1027, h572, h527,
    h427, h351296, h20243, h38, h34, h316, h3128, h116, h29, h59, h89,
    h2027, h35432, h7729, h536, h1081, h5243, h481, h332, h52, h78, h94,
    h98, h258, h1516, hL, halpha, hbeta, hgamma, hdelta, hepsilon, hzeta,
    heta, hsq, hsqB, hsqC, hsqD, hcub, hcubB, hquar, hquint, pow_two,
    pow_three, zero_mul, add_zero, mul_zero]
  rw [hXderiv, hVderiv, hUderiv, hTderiv, hSderiv, hRderiv, hQderiv, hPderiv]
  simp only [alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610, pow_two, pow_three]
  ring

end DepressedRow610Tenth

section AffineDecic610Tenth

variable {k : Type*} [Field k] [CharZero k]

/-- The `z⁰` coefficient of the affine depression of a degree-ten source. -/
theorem affineDepress_degreeTen_coeff0_610
    (p : (RatFunc k)[X]) (h r : RatFunc k) (hh : h ≠ 0)
    (hp10 : p.coeff 10 = h ^ 10)
    (hp_high : ∀ n, 10 < n → p.coeff n = 0) :
    (affineDepress68 h r p).coeff 0 =
      r ^ 10 - (p.coeff 9 / h ^ 9) * r ^ 9 +
        (p.coeff 8 / h ^ 8) * r ^ 8 -
        (p.coeff 7 / h ^ 7) * r ^ 7 +
        (p.coeff 6 / h ^ 6) * r ^ 6 -
        (p.coeff 5 / h ^ 5) * r ^ 5 +
        (p.coeff 4 / h ^ 4) * r ^ 4 -
        (p.coeff 3 / h ^ 3) * r ^ 3 +
        (p.coeff 2 / h ^ 2) * r ^ 2 -
        (p.coeff 1 / h) * r + p.coeff 0 := by
  let plow : (RatFunc k)[X] :=
    p - Polynomial.C (p.coeff 10) * Polynomial.X ^ 10 - Polynomial.C (p.coeff 9) * Polynomial.X ^ 9 -
      Polynomial.C (p.coeff 8) * Polynomial.X ^ 8 - Polynomial.C (p.coeff 7) * Polynomial.X ^ 7 -
      Polynomial.C (p.coeff 6) * Polynomial.X ^ 6 - Polynomial.C (p.coeff 5) * Polynomial.X ^ 5 -
      Polynomial.C (p.coeff 4) * Polynomial.X ^ 4 - Polynomial.C (p.coeff 3) * Polynomial.X ^ 3 -
      Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 - Polynomial.C (p.coeff 1) * Polynomial.X ^ 1
  have hplow : ∀ n, 1 ≤ n → plow.coeff n = 0 := by
    intro n hn
    simp only [plow, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    rcases Nat.eq_or_lt_of_le hn with h1 | hlt1
    · subst n; simp
    · have : 2 ≤ n := by omega
      rcases Nat.eq_or_lt_of_le this with h2 | hlt2
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
                      · subst n; simp [hp10]
                      · simp [hp_high n (by omega), show n ≠ 10 by omega,
                          show n ≠ 9 by omega, show n ≠ 8 by omega,
                          show n ≠ 7 by omega, show n ≠ 6 by omega,
                          show n ≠ 5 by omega, show n ≠ 4 by omega,
                          show n ≠ 3 by omega, show n ≠ 2 by omega,
                          show n ≠ 1 by omega]
  have hplowDeg : plow.natDegree ≤ 0 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro n hn
      exact hplow n (by omega))
  have hp_split :
      p = Polynomial.C (p.coeff 10) * Polynomial.X ^ 10 + Polynomial.C (p.coeff 9) * Polynomial.X ^ 9 +
        Polynomial.C (p.coeff 8) * Polynomial.X ^ 8 + Polynomial.C (p.coeff 7) * Polynomial.X ^ 7 +
        Polynomial.C (p.coeff 6) * Polynomial.X ^ 6 + Polynomial.C (p.coeff 5) * Polynomial.X ^ 5 +
        Polynomial.C (p.coeff 4) * Polynomial.X ^ 4 + Polynomial.C (p.coeff 3) * Polynomial.X ^ 3 +
        Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 + Polynomial.C (p.coeff 1) * Polynomial.X ^ 1 + plow := by
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
          (Polynomial.C (p.coeff 1) * Polynomial.X ^ 1).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) +
          plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) := by
    have hdef : affineDepress68 h r p =
        p.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹) := rfl
    have hsum (A B D E G H I J K M s t : (RatFunc k)[X]) :
        (A + B + D + E + G + H + I + J + K + M + s).comp t =
          A.comp t + B.comp t + D.comp t + E.comp t + G.comp t +
            H.comp t + I.comp t + J.comp t + K.comp t + M.comp t + s.comp t := by
      have h1 : (A + B + D + E + G + H + I + J + K + M + s).comp t =
          (A + B + D + E + G + H + I + J + K + M).comp t + s.comp t :=
        Polynomial.add_comp
      have h2 : (A + B + D + E + G + H + I + J + K + M).comp t =
          (A + B + D + E + G + H + I + J + K).comp t + M.comp t :=
        Polynomial.add_comp
      have h3 : (A + B + D + E + G + H + I + J + K).comp t =
          (A + B + D + E + G + H + I + J).comp t + K.comp t :=
        Polynomial.add_comp
      have h4 : (A + B + D + E + G + H + I + J).comp t =
          (A + B + D + E + G + H + I).comp t + J.comp t :=
        Polynomial.add_comp
      have h5 : (A + B + D + E + G + H + I).comp t =
          (A + B + D + E + G + H).comp t + I.comp t :=
        Polynomial.add_comp
      have h6 : (A + B + D + E + G + H).comp t =
          (A + B + D + E + G).comp t + H.comp t := Polynomial.add_comp
      have h7 : (A + B + D + E + G).comp t =
          (A + B + D + E).comp t + G.comp t := Polynomial.add_comp
      have h8 : (A + B + D + E).comp t =
          (A + B + D).comp t + E.comp t := Polynomial.add_comp
      have h9 : (A + B + D).comp t =
          (A + B).comp t + D.comp t := Polynomial.add_comp
      have h10 : (A + B).comp t = A.comp t + B.comp t := Polynomial.add_comp
      rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    exact hdef.trans ((congrArg (fun t => t.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹))
      hp_split).trans (hsum _ _ _ _ _ _ _ _ _ _ _ _))
  have hlow0 :
      (plow.comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        p.coeff 0 := by
    have hC : plow = Polynomial.C (plow.coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero hplowDeg
    have hcoeff0 : plow.coeff 0 = p.coeff 0 := by
      simp [plow]
    rw [hC, Polynomial.C_comp, Polynomial.coeff_C, if_pos rfl, hcoeff0]
  have h10_0 :
      ((Polynomial.C (p.coeff 10) * Polynomial.X ^ 10).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        r ^ 10 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 10) h r 10 0 hh]
    have hle : (0 : ℕ) ≤ 10 := by omega
    have hbin : (10 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hp10, hbin, pow_zero]
    field_simp [hh]; ring
  have h9_0 :
      ((Polynomial.C (p.coeff 9) * Polynomial.X ^ 9).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 9 / h ^ 9) * r ^ 9 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 9) h r 9 0 hh]
    have hle : (0 : ℕ) ≤ 9 := by omega
    have hbin : (9 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h8_0 :
      ((Polynomial.C (p.coeff 8) * Polynomial.X ^ 8).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        (p.coeff 8 / h ^ 8) * r ^ 8 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 8) h r 8 0 hh]
    have hle : (0 : ℕ) ≤ 8 := by omega
    have hbin : (8 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h7_0 :
      ((Polynomial.C (p.coeff 7) * Polynomial.X ^ 7).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 7 / h ^ 7) * r ^ 7 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 7) h r 7 0 hh]
    have hle : (0 : ℕ) ≤ 7 := by omega
    have hbin : (7 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h6_0 :
      ((Polynomial.C (p.coeff 6) * Polynomial.X ^ 6).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        (p.coeff 6 / h ^ 6) * r ^ 6 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 6) h r 6 0 hh]
    have hle : (0 : ℕ) ≤ 6 := by omega
    have hbin : (6 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h5_0 :
      ((Polynomial.C (p.coeff 5) * Polynomial.X ^ 5).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 5 / h ^ 5) * r ^ 5 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 5) h r 5 0 hh]
    have hle : (0 : ℕ) ≤ 5 := by omega
    have hbin : (5 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h4_0 :
      ((Polynomial.C (p.coeff 4) * Polynomial.X ^ 4).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        (p.coeff 4 / h ^ 4) * r ^ 4 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 4) h r 4 0 hh]
    have hle : (0 : ℕ) ≤ 4 := by omega
    have hbin : (4 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero]
    field_simp [hh]; ring
  have h3_0 :
      ((Polynomial.C (p.coeff 3) * Polynomial.X ^ 3).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 3 / h ^ 3) * r ^ 3 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 3) h r 3 0 hh]
    have hle : (0 : ℕ) ≤ 3 := by omega
    have hbin : (3 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero, pow_three]
    field_simp [hh]; ring
  have h2_0 :
      ((Polynomial.C (p.coeff 2) * Polynomial.X ^ 2).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        (p.coeff 2 / h ^ 2) * r ^ 2 := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 2) h r 2 0 hh]
    have hle : (0 : ℕ) ≤ 2 := by omega
    have hbin : (2 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero, pow_two]
    field_simp [hh]; ring
  have h1_0 :
      ((Polynomial.C (p.coeff 1) * Polynomial.X ^ 1).comp ((Polynomial.X - Polynomial.C r) * Polynomial.C h⁻¹)).coeff 0 =
        - (p.coeff 1 / h) * r := by
    rw [coeff_comp_C_mul_X_pow_affineScale810 (p.coeff 1) h r 1 0 hh]
    have hle : (0 : ℕ) ≤ 1 := by omega
    have hbin : (1 : ℕ).choose 0 = 1 := by decide
    simp only [hle, ite_true, hbin, pow_zero, pow_one]
    field_simp [hh]; ring
  rw [hq, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
    Polynomial.coeff_add, h10_0, h9_0, h8_0, h7_0, h6_0, h5_0, h4_0, h3_0,
    h2_0, h1_0, hlow0]
  ring

end AffineDecic610Tenth
section NonzeroTenthDefect610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 80000000 in
/-- The ninth sextic/decic integral on a square-core ninth-power source:
the cleared defect is a scalar times `h⁵⁰`. -/
theorem nonzeroFace610_tenthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ kappa : k,
      localClearedTenthDefect610 h0 (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) (q.coeff 0) lambda =
        Polynomial.C kappa * h0 ^ 50 := by
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
  let b1 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 1)
  let b0 : RatFunc k := algebraMap k[X] (RatFunc k) (q.coeff 0)
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
  have hg3 :
      g.coeff 3 =
        depressedU610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff3_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedU610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3]
  have hg1 :
      g.coeff 1 =
        depressedW610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 b2 b1 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff1_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedW610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1]
  have hg0 :
      g.coeff 0 =
        depressedX610 hRF (sexticDepressionR610 hRF a5) b9 b8 b7 b6 b5
          b4 b3 b2 b1 b0 := by
    dsimp only [g]
    rw [affineDepress_degreeTen_coeff0_610 (sourceToRatFunc68 q) hRF
      (sexticDepressionR610 hRF a5) hh hgTop hg_high_src]
    simp [depressedX610, sexticDepressionR610, sourceToRatFunc68,
      sourceToRatFunc46, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0]
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
  have hrow8 :
      (9 : RatFunc k) * g.coeff 9 * ratFuncDerivation68 (f.coeff 0) +
        (8 : RatFunc k) * g.coeff 8 * ratFuncDerivation68 (f.coeff 1) +
        (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 2) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 3) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 8) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 7) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 6) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 5) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 3) = 0 := by
    have hrow :=
      differentialJacobian_coeff_8_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 8) hbracket
    simpa [f, g, Polynomial.coeff_C, show (8 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow6 :
      (7 : RatFunc k) * g.coeff 7 * ratFuncDerivation68 (f.coeff 0) +
        (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 1) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 2) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 3) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 6) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 5) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 4) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 3) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_6_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 6) hbracket
    simpa [f, g, Polynomial.coeff_C, show (6 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow5 :
      (6 : RatFunc k) * g.coeff 6 * ratFuncDerivation68 (f.coeff 0) +
        (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 1) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 2) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 3) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 5) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 4) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 3) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 2) -
          (6 : RatFunc k) * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_5_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 5) hbracket
    simpa [f, g, Polynomial.coeff_C, show (5 : ℕ) ≠ 0 by norm_num] using
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
  have hzeta0deriv :
      ratFuncDerivation68
        (zetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 3)) = 0 :=
    zetaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 3)
      hLconst halpha0 hbeta0 hgamma0 hdelta0 (by simpa using hrow8)
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
  have hkappa0deriv :
      ratFuncDerivation68
        (iotaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 0)) = 0 :=
    iotaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 0) hLconst halpha0 hbeta0
      hgamma0 hdelta0 heps0deriv hzeta0deriv heta0deriv
      (by simpa using hrow5)
  obtain ⟨kappa0, hkappa0⟩ :
      ∃ a : k,
        iotaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 0) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hkappa0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedTenthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda) =
        (18 : RatFunc k) * hRF ^ 50 *
          iotaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 0) := by
    have hF := tenthDefect_eq_clearedIota610 hRF a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 b0 (RatFunc.C lambda) hh
      (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedTenthDefect610, map_sub, map_add, map_mul, map_pow,
      map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3, a2, a1, a0,
      b8, b7, b6, b5, b4, b3, b2, b1, b0, iotaResidual610, alphaResidual610,
      betaResidual610, gammaResidual610, deltaResidual610,
      epsilonResidual610, zetaResidual610, etaResidual610, hf4, hf3, hf2,
      hf1, hf0, hg0, hg2, hg3, hg4, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedTenthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            (q.coeff 0) lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (18 * kappa0) * h0 ^ 50) := by
    rw [hclear, hkappa0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨18 * kappa0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget
end NonzeroTenthDefect610

variable [IsAlgClosed k]

/-- Strongest exact ninth residual after the constant-scale source bridge:
the cleared weight-fifty sextic/decic defect is a scalar times `h⁵⁰`.
Both the vanishing and the nonzero values of `λ` are permitted. -/
theorem scaleZero_ninthClearedDefect_exists_C_610
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda alpha gamma delta eps zeta eta theta iota kappa : k),
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
        Polynomial.C theta * (Polynomial.C t) ^ 40 ∧
      localClearedNinthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C iota * (Polynomial.C t) ^ 45 ∧
      localClearedTenthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) (q.coeff 0) lambda =
        Polynomial.C kappa * (Polynomial.C t) ^ 50 := by
  obtain ⟨lambda, alpha, gamma, delta, eps, zeta, eta, theta, iota, hN, halpha,
      hgamma, hdelta, heps, hzeta, heta, htheta, hiota⟩ :=
    scaleZero_eighthClearedDefect_exists_C_610 hp hq hD ht hH hp6 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨kappa, hkappa⟩ :=
    nonzeroFace610_tenthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp6 hq10 hN hD
  exact ⟨lambda, alpha, gamma, delta, eps, zeta, eta, theta, iota, kappa, hN, halpha,
    hgamma, hdelta, heps, hzeta, heta, htheta, hiota, hkappa⟩

/-- Source-facing ninth residual packet for a normalized scale-zero
`(6,10)` pair.  The constants `λ`, `α`, `γ`, `δ`, `ε`, `ζ`, `η`, `θ`, `ι`, and
`κ` may vanish. -/
theorem normalized610ScaleZero_exists_ninthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda alpha gamma delta eps zeta eta theta iota kappa : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTenthDefect610 (Polynomial.C t)
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
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C kappa * (Polynomial.C t) ^ 50 := by
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
  obtain ⟨lambda, _alpha, _gamma, _delta, _eps, _zeta, _eta, _theta, _iota, kappa, hN,
      _hM, _hT, _hU, _hV, _hW, _hX, _hY, _hI, hZ⟩ :=
    scaleZero_ninthClearedDefect_exists_C_610 hp hq hD ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  exact ⟨t, lambda, 0, 0, 0, 0, 0, 0, 0, 0, kappa, ht, hHsq,
    by simpa only [p, q] using hN,
    by simpa only [p, q] using hZ⟩

/-- At scale zero the weight-fifty defect is a literal ground-field
constant. -/
theorem normalized610ScaleZero_ninthClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda theta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedTenthDefect610 (Polynomial.C t)
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
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C theta := by
  obtain ⟨t, lambda, _a, _g, _d, _e, _z, _et, _th, _iot, kappa, ht, hHsq, _hN, hY⟩ :=
    normalized610ScaleZero_exists_ninthClearedDefect hsource
  refine ⟨t, lambda, kappa * t ^ 50, ht, hHsq, ?_⟩
  have hconst :
      localClearedTenthDefect610 (Polynomial.C t)
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
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C (kappa * t ^ 50) := by
    rw [hY, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) kappa (t ^ 50)).symm
  exact hconst

/-- Newton degree of the ninth cleared sextic/decic defect at scale zero. -/
theorem normalized610ScaleZero_ninthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedTenthDefect610 (Polynomial.C t)
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
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, theta, ht, hHsq, hY⟩ :=
    normalized610ScaleZero_ninthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hY]
  exact (natDegree_C theta).le

/-- Exact ninth residual selector: `18 q₀ h⁵⁰` differs from a
polynomial in the remaining ninth-defect monomials by a ground constant. -/
theorem normalized610ScaleZero_ninthSourceResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda theta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (18 : k[X]) * q.coeff 0 * h0 ^ 50 =
        Polynomial.C theta -
          (localClearedTenthDefect610 h0 (p.coeff 5) (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
              (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
              (q.coeff 0) lambda -
            (18 : k[X]) * q.coeff 0 * h0 ^ 50) := by
  dsimp only
  obtain ⟨t, lambda, theta, ht, hHsq, hY⟩ :=
    normalized610ScaleZero_ninthClearedDefect_exists_C hsource
  refine ⟨t, lambda, theta, ht, hHsq, ?_⟩
  have hX := hY
  simp only [localClearedTenthDefect610] at hX ⊢
  linear_combination hX

/-- Aligned/nonzero split of the scale-zero ninth cleared defect: it
vanishes, or it is a nonzero ground-field constant. -/
theorem normalized610ScaleZero_ninthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let W :=
        localClearedTenthDefect610 (Polynomial.C t)
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
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda
      W = 0 ∨ ∃ theta : k, theta ≠ 0 ∧ W = Polynomial.C theta := by
  dsimp only
  obtain ⟨t, lambda, theta, ht, hHsq, hY⟩ :=
    normalized610ScaleZero_ninthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  by_cases htheta : theta = 0
  · left
    simpa only [htheta, Polynomial.C_0] using hY
  · exact Or.inr ⟨theta, htheta, hY⟩

/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-fifty defect. -/
theorem normalized610ScaleZero_ninthClearedDefectBranches
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
        localClearedTenthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
          (q.coeff 0) lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      W = Polynomial.C theta ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (theta = 0 ∧ W = 0 ∨
        theta ≠ 0 ∧ W = Polynomial.C theta) := by
  dsimp only
  obtain ⟨t, lambda, _a, _g, _d, _e, _z, _et, _th, _iot, kappa0, ht, hHsq, hN, hYpow⟩ :=
    normalized610ScaleZero_exists_ninthClearedDefect hsource
  let theta : k := kappa0 * t ^ 50
  have hY :
      localClearedTenthDefect610 (Polynomial.C t)
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
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C theta := by
    rw [hYpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) kappa0 (t ^ 50)).symm
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

/-- Aligned branch `N = 0`: the weight-fifty defect is still a ground
constant, now with `λ = 0`. -/
theorem normalized610ScaleZero_ninthClearedDefect_of_aligned
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
      localClearedTenthDefect610 (Polynomial.C t)
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
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          0 =
        Polynomial.C theta := by
  obtain ⟨t, lambda, _a, _g, _d, _e, _z, _et, _th, _iot, kappa0, ht, hHsq, hN, hYpow⟩ :=
    normalized610ScaleZero_exists_ninthClearedDefect hsource
  have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
    pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
  have hlambda : lambda = 0 := by
    have hmul : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
      hN.symm.trans haligned
    have hC : Polynomial.C lambda = 0 :=
      (mul_eq_zero.mp hmul).resolve_right ht9
    exact Polynomial.C_eq_zero.mp hC
  refine ⟨t, kappa0 * t ^ 50, ht, hHsq, ?_⟩
  have hY :
      localClearedTenthDefect610 (Polynomial.C t)
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
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          0 =
        Polynomial.C (kappa0 * t ^ 50) := by
    rw [← hlambda, hYpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) kappa0 (t ^ 50)).symm
  exact hY

/-- Nonzero discriminator branch: `λ ≠ 0` and the weight-fifty defect
is still a ground constant. -/
theorem normalized610ScaleZero_ninthClearedDefect_of_nonzero
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
      localClearedTenthDefect610 (Polynomial.C t)
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
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C theta := by
  obtain ⟨t, lambda, _a, _g, _d, _e, _z, _et, _th, _iot, kappa0, ht, hHsq, hN, hYpow⟩ :=
    normalized610ScaleZero_exists_ninthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro hzero
    apply hnonzero
    simpa only [hzero, Polynomial.C_0, zero_mul] using hN
  refine ⟨t, lambda, kappa0 * t ^ 50, ht, hlambda, hHsq, hN, ?_⟩
  have hY :
      localClearedTenthDefect610 (Polynomial.C t)
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
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 0)
          lambda =
        Polynomial.C (kappa0 * t ^ 50) := by
    rw [hYpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) kappa0 (t ^ 50)).symm
  exact hY


end ScaleZeroNinthDefect610

#print axioms normalized610ScaleZero_tenthCoefficientJacobianRow
#print axioms scaleZero_tenthCoefficientJacobianRow_610
#print axioms normalized610ScaleZero_tenthCoefficientJacobianRow_collapsed
#print axioms depressedX610_eq_cleared
#print axioms tenthDefect_eq_clearedIota610
#print axioms differentialJacobian_coeff_5_monicSexticDecic
#print axioms iotaResidual610_deriv_zero
#print axioms affineDepress_degreeTen_coeff0_610
#print axioms nonzeroFace610_tenthDefectPowerRelation
#print axioms scaleZero_ninthClearedDefect_exists_C_610
#print axioms localClearedTenthDefect610_of_lambda_zero
#print axioms normalized610ScaleZero_exists_ninthClearedDefect
#print axioms normalized610ScaleZero_ninthClearedDefect_exists_C
#print axioms normalized610ScaleZero_ninthClearedDefect_natDegree_le_zero
#print axioms normalized610ScaleZero_ninthSourceResidual
#print axioms normalized610ScaleZero_ninthClearedDefectFirstFace
#print axioms normalized610ScaleZero_ninthClearedDefectBranches
#print axioms normalized610ScaleZero_ninthClearedDefect_of_aligned
#print axioms normalized610ScaleZero_ninthClearedDefect_of_nonzero

end Max11DegreeRoutes
