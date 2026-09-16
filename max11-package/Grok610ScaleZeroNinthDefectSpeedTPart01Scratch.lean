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

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

section ScaleZeroNinthDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
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

set_option maxHeartbeats 64000000 in
/-- Depressed decic `z⁰` coefficient. -/
def depressedX610 (h r b9 b8 b7 b6 b5 b4 b3 b2 b1 b0 : F) : F :=
  r ^ 10 - (b9 / h ^ 9) * r ^ 9 + (b8 / h ^ 8) * r ^ 8 -
    (b7 / h ^ 7) * r ^ 7 + (b6 / h ^ 6) * r ^ 6 -
    (b5 / h ^ 5) * r ^ 5 + (b4 / h ^ 4) * r ^ 4 -
    (b3 / h ^ 3) * r ^ 3 + (b2 / h ^ 2) * r ^ 2 -
    (b1 / h) * r + b0

set_option maxHeartbeats 64000000 in
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

-- Fix arithmetic inference while preserving the literal public expression.
local infixl:65 (priority := high) " + " => (HAdd.hAdd (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:65 (priority := high) " - " => (HSub.hSub (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:70 (priority := high) " * " => (HMul.hMul (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:70 (priority := high) " / " => (HDiv.hDiv (α := F[X]) (β := F[X]) (γ := F[X]))
local infixr:80 (priority := high) " ^ " => (HPow.hPow (α := F[X]) (β := Nat) (γ := F[X]))
local prefix:75 (priority := high) "-" => (Neg.neg (α := F[X]))

set_option maxHeartbeats 64000000 in
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



#print axioms localClearedTenthDefect610.eq_1

end Depression610Tenth
end ScaleZeroNinthDefect610
end Max11DegreeRoutes
end
