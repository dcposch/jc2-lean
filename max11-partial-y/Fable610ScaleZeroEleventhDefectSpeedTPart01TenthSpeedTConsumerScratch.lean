import Fable610ScaleZeroTenthDefectSpeedTScratch

/-! # Scale-zero eleventh cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Fable610ScaleZeroTenthDefectScratch` on the constant core
`H = (C t)²`.  The tenth packet already forces the discriminator `N`, the
weight-fifty defect `ι`, and the weight-fifty-five defect `κ` to ground
constants, including the exact selectors `18 q₀ h⁵⁰` and
`3134566563840 p₀ q₅ h⁵⁰`.  This file consumes the next unused Keller
coefficient, the degree-`3` Jacobian row

```
(p₃)' (1 q₁) + (p₂)' (2 q₂) + (p₁)' (3 q₃) + (p₀)' (4 q₄)
  - (4 p₄) q₀' - (3 p₃) q₁' - (2 p₂) q₂' - (1 p₁) q₃' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is
`4 T E' + 3 U D' + 2 V C' + W B' - D U' - 2 C V' - 3 B W' - 4 A X' = 0`.
The derivative `X'` is eliminated through the degree-`5` row, so the
first integral `λ` of the degree-`3` row uses only the second- through
ninth-face integrals; it clears to the weight-sixty polynomial defect,
and at scale zero that defect is again a ground-field constant.

The `λ` formula, its weight-sixty clearing by `258280326 h⁶⁰`, the
solved derivative forms, and the aligned `179`-monomial specialization
were derived and cross-checked independently (closedness of the reduced
row `1`-form, the identity `d λ = (1/6) · row`, and a rational
end-to-end evaluation of the cleared polynomial).  The
derivation-in-zero reduction keeps the sub-residuals opaque so the
tower hypotheses fire, and supplies the complete constant-derivative
kill set from `d (1/4) = 0` through `d (385/7776) = 0` and `d (A⁶)`,
`d (B⁴)`, `d (E²)`.

The degree-`5` iota first integral, the exact `18 q₀ h⁵⁰` residual, and
the degree-`4` kappa selector `3134566563840 p₀ q₅ h⁵⁰` are preserved
and not cleared to zero.  No total-degree or twice-prime theorem is
used.  A constant scale has no finite root, so no root-jet packet
exists at this scale.  Both the vanishing and the nonzero constant
branches of `λ` and of the weight-fifty-five and weight-sixty defects
are kept.  The packet does not close the leaf: unused Jacobian
coefficients start at degree `2`.
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

section ScaleZeroEleventhDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/


set_option maxHeartbeats 64000000 in
/-- The twelfth row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  Unused Jacobian coefficients of the tenth packet
start at degree `3`. -/
theorem scaleZeroRaw_twelfthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : K)) -
      ((p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 3) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (3 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 3 :
      Finset (ℕ × ℕ)) =
      ({(0, 3), (1, 2), (2, 1), (3, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  have hC4 : Polynomial.C (4 : K) = (4 : K[X]) :=
    Polynomial.C_eq_natCast 4
  rw [hC2, hC3, hC4]
  linear_combination hcoeff

set_option maxHeartbeats 64000000 in
/-- Source-facing degree-`3` Jacobian row of a normalized scale-zero
`(6,10)` pair. -/
theorem normalized610ScaleZero_twelfthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : k)) -
      ((p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) =
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
    scaleZeroRaw_twelfthCoefficientJacobianRow_610 hp hq hjac

set_option maxHeartbeats 64000000 in
/-- At scale zero the common core is constant; the degree-`3` row has no
`p₆'`, `p₅'`, `q₁₀'`, or `q₉'` term, so it collapses to the same literal
row. -/
theorem scaleZero_twelfthCoefficientJacobianRow_610
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : k)) -
      ((p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp6der : (p.coeff 6).derivative = 0 := by
    rw [hp6, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := scaleZeroRaw_twelfthCoefficientJacobianRow_610 hp hq hjac
  simpa [hp6der, hq10der] using hrow

set_option maxHeartbeats 64000000 in
/-- Source-facing scale-zero collapse of the degree-`3` row. -/
theorem normalized610ScaleZero_twelfthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 3).derivative * q.coeff 1 +
        (p.coeff 2).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 1).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 0).derivative * (q.coeff 4 * Polynomial.C (4 : k)) -
      ((p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 0).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 1).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 2).derivative +
        p.coeff 1 * (q.coeff 3).derivative) =
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
    scaleZero_twelfthCoefficientJacobianRow_610 hp hq hjac hHdegree
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)

/-! ## Weight-sixty cleared defect after a square root of the core -/

section Depression610Twelfth

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 64000000 in
/-- First residual of the degree-`3` row, with `X'` eliminated through
the degree-`5` row.  Equivalent to
`(1/6) B θ - (1/9) A² η + (1/3) C η - (1/4) A B ζ + (1/2) D ζ
+ (4/81) A³ ε - (2/9) A C ε - (1/9) B² ε + (2/3) E ε + (35/432) A² B δ
- (5/36) A D δ - (5/36) B C δ - (8/729) A⁵ α + (20/243) A³ C α
+ (10/81) A² B² α - (4/27) A² E α - (8/27) A B D α - (4/27) A C² α
- (4/27) B² C α + (4/9) C E α + (2/9) D² α + (385/7776) A³ B β
- (35/432) A² D β - (35/216) A B C β - (35/1296) B³ β + (7/36) B E β
+ (7/36) C D β - (15/256) L A⁴ B + (3/32) L A³ D + (9/32) L A² B C
+ (3/32) L A B³ - (3/8) L A B E - (3/8) L A C D - (3/16) L B² D
- (3/16) L B C² + (3/4) L D E + (35/6561) A⁶ - (35/729) A⁴ C
- (70/729) A³ B² + (20/243) A³ E + (20/81) A² B D + (10/81) A² C²
+ (20/81) A B² C - (10/27) A C E - (5/27) A D² + (5/243) B⁴
- (5/27) B² E - (10/27) B C D - (5/81) C³ + (5/9) E²`
on the second- through ninth-face integrals. -/
def lambdaResidual610
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  (1 / 6 : F) * B * thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0 -
    (1 / 9 : F) * A ^ 2 * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 +
    (1 / 3 : F) * C0 * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 -
    (1 / 4 : F) * A * B * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 +
    (1 / 2 : F) * D0 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 +
    (4 / 81 : F) * A ^ 3 * epsilonResidual610 L A B C0 D0 E0 P Q R T0 -
    (2 / 9 : F) * A * C0 * epsilonResidual610 L A B C0 D0 E0 P Q R T0 -
    (1 / 9 : F) * B ^ 2 * epsilonResidual610 L A B C0 D0 E0 P Q R T0 +
    (2 / 3 : F) * E0 * epsilonResidual610 L A B C0 D0 E0 P Q R T0 +
    (35 / 432 : F) * A ^ 2 * B * deltaResidual610 L A B C0 D0 P Q S0 -
    (5 / 36 : F) * A * D0 * deltaResidual610 L A B C0 D0 P Q S0 -
    (5 / 36 : F) * B * C0 * deltaResidual610 L A B C0 D0 P Q S0 -
    (8 / 729 : F) * A ^ 5 * alphaResidual610 A P +
    (20 / 243 : F) * A ^ 3 * C0 * alphaResidual610 A P +
    (10 / 81 : F) * A ^ 2 * B ^ 2 * alphaResidual610 A P -
    (4 / 27 : F) * A ^ 2 * E0 * alphaResidual610 A P -
    (8 / 27 : F) * A * B * D0 * alphaResidual610 A P -
    (4 / 27 : F) * A * C0 ^ 2 * alphaResidual610 A P -
    (4 / 27 : F) * B ^ 2 * C0 * alphaResidual610 A P +
    (4 / 9 : F) * C0 * E0 * alphaResidual610 A P +
    (2 / 9 : F) * D0 ^ 2 * alphaResidual610 A P +
    (385 / 7776 : F) * A ^ 3 * B * betaResidual610 L A B Q -
    (35 / 432 : F) * A ^ 2 * D0 * betaResidual610 L A B Q -
    (35 / 216 : F) * A * B * C0 * betaResidual610 L A B Q -
    (35 / 1296 : F) * B ^ 3 * betaResidual610 L A B Q +
    (7 / 36 : F) * B * E0 * betaResidual610 L A B Q +
    (7 / 36 : F) * C0 * D0 * betaResidual610 L A B Q -
    (15 / 256 : F) * L * A ^ 4 * B +
    (3 / 32 : F) * L * A ^ 3 * D0 +
    (9 / 32 : F) * L * A ^ 2 * B * C0 +
    (3 / 32 : F) * L * A * B ^ 3 -
    (3 / 8 : F) * L * A * B * E0 -
    (3 / 8 : F) * L * A * C0 * D0 -
    (3 / 16 : F) * L * B ^ 2 * D0 -
    (3 / 16 : F) * L * B * C0 ^ 2 +
    (3 / 4 : F) * L * D0 * E0 +
    (35 / 6561 : F) * A ^ 6 -
    (35 / 729 : F) * A ^ 4 * C0 -
    (70 / 729 : F) * A ^ 3 * B ^ 2 +
    (20 / 243 : F) * A ^ 3 * E0 +
    (20 / 81 : F) * A ^ 2 * B * D0 +
    (10 / 81 : F) * A ^ 2 * C0 ^ 2 +
    (20 / 81 : F) * A * B ^ 2 * C0 -
    (10 / 27 : F) * A * C0 * E0 -
    (5 / 27 : F) * A * D0 ^ 2 +
    (5 / 243 : F) * B ^ 4 -
    (5 / 27 : F) * B ^ 2 * E0 -
    (10 / 27 : F) * B * C0 * D0 -
    (5 / 81 : F) * C0 ^ 3 +
    (5 / 9 : F) * E0 ^ 2

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 10. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk01
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    (8107385 : F[X]) * a5 ^ 12
    - (3979989 : F[X]) * a5 ^ 11 * h ^ 5 * Polynomial.C lambda
    - (80514720 : F[X]) * a4 * a5 ^ 10 * h ^ 6
    - (12077208 : F[X]) * a5 ^ 10 * b8 * h ^ 2
    + (84192075 : F[X]) * a3 * a5 ^ 9 * h ^ 12
    + (45289530 : F[X]) * a4 * a5 ^ 9 * h ^ 11 * Polynomial.C lambda
    + (12193335 : F[X]) * a5 ^ 9 * b7 * h ^ 8
    - (88609950 : F[X]) * a2 * a5 ^ 8 * h ^ 18
    - (47031435 : F[X]) * a3 * a5 ^ 8 * h ^ 17 * Polynomial.C lambda
    + (261285750 : F[X]) * a4 ^ 2 * a5 ^ 8 * h ^ 12

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 20. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk02 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (125417160 : F[X]) * a4 * a5 ^ 8 * b8 * h ^ 8
    - (12269070 : F[X]) * a5 ^ 8 * b6 * h ^ 14
    + (94062870 : F[X]) * a1 * a5 ^ 7 * h ^ 24
    + (49076280 : F[X]) * a2 * a5 ^ 7 * h ^ 23 * Polynomial.C lambda
    - (463498200 : F[X]) * a3 * a4 * a5 ^ 7 * h ^ 18
    - (130870080 : F[X]) * a3 * a5 ^ 7 * b8 * h ^ 14
    - (188125740 : F[X]) * a4 ^ 2 * a5 ^ 7 * h ^ 17 * Polynomial.C lambda
    - (114511320 : F[X]) * a4 * a5 ^ 7 * b7 * h ^ 14
    + (12269070 : F[X]) * a5 ^ 7 * b5 * h ^ 20
    - (101039400 : F[X]) * a0 * a5 ^ 6 * h ^ 30

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 30. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk03 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (51530094 : F[X]) * a1 * a5 ^ 6 * h ^ 29 * Polynomial.C lambda
    + (400789620 : F[X]) * a2 * a4 * a5 ^ 6 * h ^ 24
    + (137413584 : F[X]) * a2 * a5 ^ 6 * b8 * h ^ 20
    + (200394810 : F[X]) * a3 ^ 2 * a5 ^ 6 * h ^ 24
    + (343533960 : F[X]) * a3 * a4 * a5 ^ 6 * h ^ 23 * Polynomial.C lambda
    + (120236886 : F[X]) * a3 * a5 ^ 6 * b7 * h ^ 20
    - (254469600 : F[X]) * a4 ^ 3 * a5 ^ 6 * h ^ 18
    - (458045280 : F[X]) * a4 ^ 2 * a5 ^ 6 * b8 * h ^ 14
    + (103060188 : F[X]) * a4 * a5 ^ 6 * b6 * h ^ 20
    - (12124728 : F[X]) * a5 ^ 6 * b4 * h ^ 26

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 40. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk04 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (54561276 : F[X]) * a0 * a5 ^ 5 * h ^ 35 * Polynomial.C lambda
    - (333430020 : F[X]) * a1 * a4 * a5 ^ 5 * h ^ 30
    - (145496736 : F[X]) * a1 * a5 ^ 5 * b8 * h ^ 26
    - (333430020 : F[X]) * a2 * a3 * a5 ^ 5 * h ^ 30
    - (309180564 : F[X]) * a2 * a4 * a5 ^ 5 * h ^ 29 * Polynomial.C lambda
    - (127309644 : F[X]) * a2 * a5 ^ 5 * b7 * h ^ 26
    - (154590282 : F[X]) * a3 ^ 2 * a5 ^ 5 * h ^ 29 * Polynomial.C lambda
    + (429417450 : F[X]) * a3 * a4 ^ 2 * a5 ^ 5 * h ^ 24
    + (824481504 : F[X]) * a3 * a4 * a5 ^ 5 * b8 * h ^ 20
    - (109122552 : F[X]) * a3 * a5 ^ 5 * b6 * h ^ 26

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 50. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk05 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (343533960 : F[X]) * a4 ^ 3 * a5 ^ 5 * h ^ 23 * Polynomial.C lambda
    + (360710658 : F[X]) * a4 ^ 2 * a5 ^ 5 * b7 * h ^ 20
    - (90935460 : F[X]) * a4 * a5 ^ 5 * b5 * h ^ 26
    + (11691702 : F[X]) * a5 ^ 5 * b3 * h ^ 32
    + (259815600 : F[X]) * a0 * a4 * a5 ^ 4 * h ^ 36
    + (155889360 : F[X]) * a0 * a5 ^ 4 * b8 * h ^ 32
    + (259815600 : F[X]) * a1 * a3 * a5 ^ 4 * h ^ 36
    + (272806380 : F[X]) * a1 * a4 * a5 ^ 4 * h ^ 35 * Polynomial.C lambda
    + (136403190 : F[X]) * a1 * a5 ^ 4 * b7 * h ^ 32
    + (129907800 : F[X]) * a2 ^ 2 * a5 ^ 4 * h ^ 36

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 60. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk06 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (272806380 : F[X]) * a2 * a3 * a5 ^ 4 * h ^ 35 * Polynomial.C lambda
    - (151559100 : F[X]) * a2 * a4 ^ 2 * a5 ^ 4 * h ^ 30
    - (727483680 : F[X]) * a2 * a4 * a5 ^ 4 * b8 * h ^ 26
    + (116917020 : F[X]) * a2 * a5 ^ 4 * b6 * h ^ 32
    - (151559100 : F[X]) * a3 ^ 2 * a4 * a5 ^ 4 * h ^ 30
    - (363741840 : F[X]) * a3 ^ 2 * a5 ^ 4 * b8 * h ^ 26
    - (772951410 : F[X]) * a3 * a4 ^ 2 * a5 ^ 4 * h ^ 29 * Polynomial.C lambda
    - (636548220 : F[X]) * a3 * a4 * a5 ^ 4 * b7 * h ^ 26
    + (97430850 : F[X]) * a3 * a5 ^ 4 * b5 * h ^ 32
    - (143139150 : F[X]) * a4 ^ 4 * a5 ^ 4 * h ^ 24

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 70. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk07 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (687067920 : F[X]) * a4 ^ 3 * a5 ^ 4 * b8 * h ^ 20
    - (272806380 : F[X]) * a4 ^ 2 * a5 ^ 4 * b6 * h ^ 26
    + (77944680 : F[X]) * a4 * a5 ^ 4 * b4 * h ^ 32
    - (10628820 : F[X]) * a5 ^ 4 * b2 * h ^ 38
    - (177147000 : F[X]) * a0 * a3 * a5 ^ 3 * h ^ 42
    - (233834040 : F[X]) * a0 * a4 * a5 ^ 3 * h ^ 41 * Polynomial.C lambda
    - (148803480 : F[X]) * a0 * a5 ^ 3 * b7 * h ^ 38
    - (177147000 : F[X]) * a1 * a2 * a5 ^ 3 * h ^ 42
    - (233834040 : F[X]) * a1 * a3 * a5 ^ 3 * h ^ 41 * Polynomial.C lambda
    - (64953900 : F[X]) * a1 * a4 ^ 2 * a5 ^ 3 * h ^ 36

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 80. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk08 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (623557440 : F[X]) * a1 * a4 * a5 ^ 3 * b8 * h ^ 32
    - (127545840 : F[X]) * a1 * a5 ^ 3 * b6 * h ^ 38
    - (116917020 : F[X]) * a2 ^ 2 * a5 ^ 3 * h ^ 41 * Polynomial.C lambda
    - (129907800 : F[X]) * a2 * a3 * a4 * a5 ^ 3 * h ^ 36
    + (623557440 : F[X]) * a2 * a3 * a5 ^ 3 * b8 * h ^ 32
    + (545612760 : F[X]) * a2 * a4 ^ 2 * a5 ^ 3 * h ^ 35 * Polynomial.C lambda
    + (545612760 : F[X]) * a2 * a4 * a5 ^ 3 * b7 * h ^ 32
    - (106288200 : F[X]) * a2 * a5 ^ 3 * b5 * h ^ 38
    - (21651300 : F[X]) * a3 ^ 3 * a5 ^ 3 * h ^ 36
    + (545612760 : F[X]) * a3 ^ 2 * a4 * a5 ^ 3 * h ^ 35 * Polynomial.C lambda

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 90. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk09 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (272806380 : F[X]) * a3 ^ 2 * a5 ^ 3 * b7 * h ^ 32
    + (707275800 : F[X]) * a3 * a4 ^ 3 * a5 ^ 3 * h ^ 30
    - (1454967360 : F[X]) * a3 * a4 ^ 2 * a5 ^ 3 * b8 * h ^ 26
    + (467668080 : F[X]) * a3 * a4 * a5 ^ 3 * b6 * h ^ 32
    - (85030560 : F[X]) * a3 * a5 ^ 3 * b4 * h ^ 38
    - (257650470 : F[X]) * a4 ^ 4 * a5 ^ 3 * h ^ 29 * Polynomial.C lambda
    - (424365480 : F[X]) * a4 ^ 3 * a5 ^ 3 * b7 * h ^ 26
    + (194861700 : F[X]) * a4 ^ 2 * a5 ^ 3 * b5 * h ^ 32
    - (63772920 : F[X]) * a4 * a5 ^ 3 * b3 * h ^ 38
    + (7971615 : F[X]) * a5 ^ 3 * b1 * h ^ 44

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 100. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk10 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (79716150 : F[X]) * a0 * a2 * a5 ^ 2 * h ^ 48
    + (191318760 : F[X]) * a0 * a3 * a5 ^ 2 * h ^ 47 * Polynomial.C lambda
    + (212576400 : F[X]) * a0 * a4 ^ 2 * a5 ^ 2 * h ^ 42
    - (510183360 : F[X]) * a0 * a4 * a5 ^ 2 * b8 * h ^ 38
    + (143489070 : F[X]) * a0 * a5 ^ 2 * b6 * h ^ 44
    + (39858075 : F[X]) * a1 ^ 2 * a5 ^ 2 * h ^ 48
    + (191318760 : F[X]) * a1 * a2 * a5 ^ 2 * h ^ 47 * Polynomial.C lambda
    + (425152800 : F[X]) * a1 * a3 * a4 * a5 ^ 2 * h ^ 42
    - (510183360 : F[X]) * a1 * a3 * a5 ^ 2 * b8 * h ^ 38
    - (350751060 : F[X]) * a1 * a4 ^ 2 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 110. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk11 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (446410440 : F[X]) * a1 * a4 * a5 ^ 2 * b7 * h ^ 38
    + (119574225 : F[X]) * a1 * a5 ^ 2 * b5 * h ^ 44
    + (212576400 : F[X]) * a2 ^ 2 * a4 * a5 ^ 2 * h ^ 42
    - (255091680 : F[X]) * a2 ^ 2 * a5 ^ 2 * b8 * h ^ 38
    + (212576400 : F[X]) * a2 * a3 ^ 2 * a5 ^ 2 * h ^ 42
    - (701502120 : F[X]) * a2 * a3 * a4 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda
    - (446410440 : F[X]) * a2 * a3 * a5 ^ 2 * b7 * h ^ 38
    - (649539000 : F[X]) * a2 * a4 ^ 3 * a5 ^ 2 * h ^ 36
    + (935336160 : F[X]) * a2 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 32
    - (382637520 : F[X]) * a2 * a4 * a5 ^ 2 * b6 * h ^ 38

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 120. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk12 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (95659380 : F[X]) * a2 * a5 ^ 2 * b4 * h ^ 44
    - (116917020 : F[X]) * a3 ^ 3 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda
    - (974308500 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 ^ 2 * h ^ 36
    + (935336160 : F[X]) * a3 ^ 2 * a4 * a5 ^ 2 * b8 * h ^ 32
    - (191318760 : F[X]) * a3 ^ 2 * a5 ^ 2 * b6 * h ^ 38
    + (545612760 : F[X]) * a3 * a4 ^ 3 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    + (818419140 : F[X]) * a3 * a4 ^ 2 * a5 ^ 2 * b7 * h ^ 32
    - (318864600 : F[X]) * a3 * a4 * a5 ^ 2 * b5 * h ^ 38
    + (71744535 : F[X]) * a3 * a5 ^ 2 * b3 * h ^ 44
    + (242494560 : F[X]) * a4 ^ 5 * a5 ^ 2 * h ^ 30

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 130. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk13 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (363741840 : F[X]) * a4 ^ 4 * a5 ^ 2 * b8 * h ^ 26
    + (233834040 : F[X]) * a4 ^ 3 * a5 ^ 2 * b6 * h ^ 32
    - (127545840 : F[X]) * a4 ^ 2 * a5 ^ 2 * b4 * h ^ 38
    + (47829690 : F[X]) * a4 * a5 ^ 2 * b2 * h ^ 44
    + (47829690 : F[X]) * a0 * a1 * a5 * h ^ 54
    - (143489070 : F[X]) * a0 * a2 * a5 * h ^ 53 * Polynomial.C lambda
    - (558013050 : F[X]) * a0 * a3 * a4 * a5 * h ^ 48
    + (382637520 : F[X]) * a0 * a3 * a5 * b8 * h ^ 44
    + (191318760 : F[X]) * a0 * a4 ^ 2 * a5 * h ^ 47 * Polynomial.C lambda
    + (334807830 : F[X]) * a0 * a4 * a5 * b7 * h ^ 44

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 140. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk14 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (143489070 : F[X]) * a0 * a5 * b5 * h ^ 50
    - (71744535 : F[X]) * a1 ^ 2 * a5 * h ^ 53 * Polynomial.C lambda
    - (558013050 : F[X]) * a1 * a2 * a4 * a5 * h ^ 48
    + (382637520 : F[X]) * a1 * a2 * a5 * b8 * h ^ 44
    - (279006525 : F[X]) * a1 * a3 ^ 2 * a5 * h ^ 48
    + (382637520 : F[X]) * a1 * a3 * a4 * a5 * h ^ 47 * Polynomial.C lambda
    + (334807830 : F[X]) * a1 * a3 * a5 * b7 * h ^ 44
    + (460582200 : F[X]) * a1 * a4 ^ 3 * a5 * h ^ 42
    - (510183360 : F[X]) * a1 * a4 ^ 2 * a5 * b8 * h ^ 38
    + (286978140 : F[X]) * a1 * a4 * a5 * b6 * h ^ 44

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 150. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk15 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (114791256 : F[X]) * a1 * a5 * b4 * h ^ 50
    - (279006525 : F[X]) * a2 ^ 2 * a3 * a5 * h ^ 48
    + (191318760 : F[X]) * a2 ^ 2 * a4 * a5 * h ^ 47 * Polynomial.C lambda
    + (167403915 : F[X]) * a2 ^ 2 * a5 * b7 * h ^ 44
    + (191318760 : F[X]) * a2 * a3 ^ 2 * a5 * h ^ 47 * Polynomial.C lambda
    + (1381746600 : F[X]) * a2 * a3 * a4 ^ 2 * a5 * h ^ 42
    - (1020366720 : F[X]) * a2 * a3 * a4 * a5 * b8 * h ^ 38
    + (286978140 : F[X]) * a2 * a3 * a5 * b6 * h ^ 44
    - (233834040 : F[X]) * a2 * a4 ^ 3 * a5 * h ^ 41 * Polynomial.C lambda
    - (446410440 : F[X]) * a2 * a4 ^ 2 * a5 * b7 * h ^ 38

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 160. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk16 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (239148450 : F[X]) * a2 * a4 * a5 * b5 * h ^ 44
    - (86093442 : F[X]) * a2 * a5 * b3 * h ^ 50
    + (460582200 : F[X]) * a3 ^ 3 * a4 * a5 * h ^ 42
    - (170061120 : F[X]) * a3 ^ 3 * a5 * b8 * h ^ 38
    - (350751060 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 * h ^ 41 * Polynomial.C lambda
    - (446410440 : F[X]) * a3 ^ 2 * a4 * a5 * b7 * h ^ 38
    + (119574225 : F[X]) * a3 ^ 2 * a5 * b5 * h ^ 44
    - (617062050 : F[X]) * a3 * a4 ^ 4 * a5 * h ^ 36
    + (623557440 : F[X]) * a3 * a4 ^ 3 * a5 * b8 * h ^ 32
    - (382637520 : F[X]) * a3 * a4 ^ 2 * a5 * b6 * h ^ 38

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 170. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk17 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (191318760 : F[X]) * a3 * a4 * a5 * b4 * h ^ 44
    - (57395628 : F[X]) * a3 * a5 * b2 * h ^ 50
    + (54561276 : F[X]) * a4 ^ 5 * a5 * h ^ 35 * Polynomial.C lambda
    + (136403190 : F[X]) * a4 ^ 4 * a5 * b7 * h ^ 32
    - (106288200 : F[X]) * a4 ^ 3 * a5 * b5 * h ^ 38
    + (71744535 : F[X]) * a4 ^ 2 * a5 * b3 * h ^ 44
    - (28697814 : F[X]) * a4 * a5 * b1 * h ^ 50
    - (143489070 : F[X]) * a0 ^ 2 * h ^ 60
    + (86093442 : F[X]) * a0 * a1 * h ^ 59 * Polynomial.C lambda
    + (478296900 : F[X]) * a0 * a2 * a4 * h ^ 54

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 180. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk18 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (229582512 : F[X]) * a0 * a2 * b8 * h ^ 50
    + (239148450 : F[X]) * a0 * a3 ^ 2 * h ^ 54
    - (143489070 : F[X]) * a0 * a3 * a4 * h ^ 53 * Polynomial.C lambda
    - (200884698 : F[X]) * a0 * a3 * b7 * h ^ 50
    - (212576400 : F[X]) * a0 * a4 ^ 3 * h ^ 48
    + (191318760 : F[X]) * a0 * a4 ^ 2 * b8 * h ^ 44
    - (172186884 : F[X]) * a0 * a4 * b6 * h ^ 50
    + (172186884 : F[X]) * a0 * b4 * h ^ 56
    + (239148450 : F[X]) * a1 ^ 2 * a4 * h ^ 54
    - (114791256 : F[X]) * a1 ^ 2 * b8 * h ^ 50

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 190. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk19 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (478296900 : F[X]) * a1 * a2 * a3 * h ^ 54
    - (143489070 : F[X]) * a1 * a2 * a4 * h ^ 53 * Polynomial.C lambda
    - (200884698 : F[X]) * a1 * a2 * b7 * h ^ 50
    - (71744535 : F[X]) * a1 * a3 ^ 2 * h ^ 53 * Polynomial.C lambda
    - (637729200 : F[X]) * a1 * a3 * a4 ^ 2 * h ^ 48
    + (382637520 : F[X]) * a1 * a3 * a4 * b8 * h ^ 44
    - (172186884 : F[X]) * a1 * a3 * b6 * h ^ 50
    + (63772920 : F[X]) * a1 * a4 ^ 3 * h ^ 47 * Polynomial.C lambda
    + (167403915 : F[X]) * a1 * a4 ^ 2 * b7 * h ^ 44
    - (143489070 : F[X]) * a1 * a4 * b5 * h ^ 50

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 200. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk20 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (129140163 : F[X]) * a1 * b3 * h ^ 56
    + (79716150 : F[X]) * a2 ^ 3 * h ^ 54
    - (71744535 : F[X]) * a2 ^ 2 * a3 * h ^ 53 * Polynomial.C lambda
    - (318864600 : F[X]) * a2 ^ 2 * a4 ^ 2 * h ^ 48
    + (191318760 : F[X]) * a2 ^ 2 * a4 * b8 * h ^ 44
    - (86093442 : F[X]) * a2 ^ 2 * b6 * h ^ 50
    - (637729200 : F[X]) * a2 * a3 ^ 2 * a4 * h ^ 48
    + (191318760 : F[X]) * a2 * a3 ^ 2 * b8 * h ^ 44
    + (191318760 : F[X]) * a2 * a3 * a4 ^ 2 * h ^ 47 * Polynomial.C lambda
    + (334807830 : F[X]) * a2 * a3 * a4 * b7 * h ^ 44

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 210. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk21 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (143489070 : F[X]) * a2 * a3 * b5 * h ^ 50
    + (194861700 : F[X]) * a2 * a4 ^ 4 * h ^ 42
    - (170061120 : F[X]) * a2 * a4 ^ 3 * b8 * h ^ 38
    + (143489070 : F[X]) * a2 * a4 ^ 2 * b6 * h ^ 44
    - (114791256 : F[X]) * a2 * a4 * b4 * h ^ 50
    + (86093442 : F[X]) * a2 * b2 * h ^ 56
    - (53144100 : F[X]) * a3 ^ 4 * h ^ 48
    + (63772920 : F[X]) * a3 ^ 3 * a4 * h ^ 47 * Polynomial.C lambda
    + (55801305 : F[X]) * a3 ^ 3 * b7 * h ^ 44
    + (389723400 : F[X]) * a3 ^ 2 * a4 ^ 3 * h ^ 42

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 220. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk22 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (255091680 : F[X]) * a3 ^ 2 * a4 ^ 2 * b8 * h ^ 38
    + (143489070 : F[X]) * a3 ^ 2 * a4 * b6 * h ^ 44
    - (57395628 : F[X]) * a3 ^ 2 * b4 * h ^ 50
    - (58458510 : F[X]) * a3 * a4 ^ 4 * h ^ 41 * Polynomial.C lambda
    - (148803480 : F[X]) * a3 * a4 ^ 3 * b7 * h ^ 38
    + (119574225 : F[X]) * a3 * a4 ^ 2 * b5 * h ^ 44
    - (86093442 : F[X]) * a3 * a4 * b3 * h ^ 50
    + (43046721 : F[X]) * a3 * b1 * h ^ 56
    - (30311820 : F[X]) * a4 ^ 6 * h ^ 36
    + (31177872 : F[X]) * a4 ^ 5 * b8 * h ^ 32

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 223. -/
private abbrev fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk23 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (31886460 : F[X]) * a4 ^ 4 * b6 * h ^ 38
    + (31886460 : F[X]) * a4 ^ 3 * b4 * h ^ 44
    - (28697814 : F[X]) * a4 ^ 2 * b2 * h ^ 50

set_option maxHeartbeats 64000000 in
/-- Polynomial numerator of `258280326 h⁶⁰ λ` on the ninth-power face. -/
def localClearedTwelfthDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk23
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk22
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk21
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk20
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk19
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk18
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk17
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk16
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk15
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk14
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk13
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk12
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk11
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk10
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk09
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk08
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk07
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk06
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk05
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk04
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk03
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk02
      (fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk01 h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda

set_option maxHeartbeats 64000000 in
/-- Aligned specialization of the weight-sixty defect: the `λ`-monomials
drop. -/
theorem localClearedTwelfthDefect610_of_lambda_zero
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) :
    localClearedTwelfthDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3
        b2 b1 0 =
    (8107385 : F[X]) * a5 ^ 12
    - (80514720 : F[X]) * a4 * a5 ^ 10 * h ^ 6
    - (12077208 : F[X]) * a5 ^ 10 * b8 * h ^ 2
    + (84192075 : F[X]) * a3 * a5 ^ 9 * h ^ 12
    + (12193335 : F[X]) * a5 ^ 9 * b7 * h ^ 8
    - (88609950 : F[X]) * a2 * a5 ^ 8 * h ^ 18
    + (261285750 : F[X]) * a4 ^ 2 * a5 ^ 8 * h ^ 12
    + (125417160 : F[X]) * a4 * a5 ^ 8 * b8 * h ^ 8
    - (12269070 : F[X]) * a5 ^ 8 * b6 * h ^ 14
    + (94062870 : F[X]) * a1 * a5 ^ 7 * h ^ 24
    - (463498200 : F[X]) * a3 * a4 * a5 ^ 7 * h ^ 18
    - (130870080 : F[X]) * a3 * a5 ^ 7 * b8 * h ^ 14
    - (114511320 : F[X]) * a4 * a5 ^ 7 * b7 * h ^ 14
    + (12269070 : F[X]) * a5 ^ 7 * b5 * h ^ 20
    - (101039400 : F[X]) * a0 * a5 ^ 6 * h ^ 30
    + (400789620 : F[X]) * a2 * a4 * a5 ^ 6 * h ^ 24
    + (137413584 : F[X]) * a2 * a5 ^ 6 * b8 * h ^ 20
    + (200394810 : F[X]) * a3 ^ 2 * a5 ^ 6 * h ^ 24
    + (120236886 : F[X]) * a3 * a5 ^ 6 * b7 * h ^ 20
    - (254469600 : F[X]) * a4 ^ 3 * a5 ^ 6 * h ^ 18
    - (458045280 : F[X]) * a4 ^ 2 * a5 ^ 6 * b8 * h ^ 14
    + (103060188 : F[X]) * a4 * a5 ^ 6 * b6 * h ^ 20
    - (12124728 : F[X]) * a5 ^ 6 * b4 * h ^ 26
    - (333430020 : F[X]) * a1 * a4 * a5 ^ 5 * h ^ 30
    - (145496736 : F[X]) * a1 * a5 ^ 5 * b8 * h ^ 26
    - (333430020 : F[X]) * a2 * a3 * a5 ^ 5 * h ^ 30
    - (127309644 : F[X]) * a2 * a5 ^ 5 * b7 * h ^ 26
    + (429417450 : F[X]) * a3 * a4 ^ 2 * a5 ^ 5 * h ^ 24
    + (824481504 : F[X]) * a3 * a4 * a5 ^ 5 * b8 * h ^ 20
    - (109122552 : F[X]) * a3 * a5 ^ 5 * b6 * h ^ 26
    + (360710658 : F[X]) * a4 ^ 2 * a5 ^ 5 * b7 * h ^ 20
    - (90935460 : F[X]) * a4 * a5 ^ 5 * b5 * h ^ 26
    + (11691702 : F[X]) * a5 ^ 5 * b3 * h ^ 32
    + (259815600 : F[X]) * a0 * a4 * a5 ^ 4 * h ^ 36
    + (155889360 : F[X]) * a0 * a5 ^ 4 * b8 * h ^ 32
    + (259815600 : F[X]) * a1 * a3 * a5 ^ 4 * h ^ 36
    + (136403190 : F[X]) * a1 * a5 ^ 4 * b7 * h ^ 32
    + (129907800 : F[X]) * a2 ^ 2 * a5 ^ 4 * h ^ 36
    - (151559100 : F[X]) * a2 * a4 ^ 2 * a5 ^ 4 * h ^ 30
    - (727483680 : F[X]) * a2 * a4 * a5 ^ 4 * b8 * h ^ 26
    + (116917020 : F[X]) * a2 * a5 ^ 4 * b6 * h ^ 32
    - (151559100 : F[X]) * a3 ^ 2 * a4 * a5 ^ 4 * h ^ 30
    - (363741840 : F[X]) * a3 ^ 2 * a5 ^ 4 * b8 * h ^ 26
    - (636548220 : F[X]) * a3 * a4 * a5 ^ 4 * b7 * h ^ 26
    + (97430850 : F[X]) * a3 * a5 ^ 4 * b5 * h ^ 32
    - (143139150 : F[X]) * a4 ^ 4 * a5 ^ 4 * h ^ 24
    + (687067920 : F[X]) * a4 ^ 3 * a5 ^ 4 * b8 * h ^ 20
    - (272806380 : F[X]) * a4 ^ 2 * a5 ^ 4 * b6 * h ^ 26
    + (77944680 : F[X]) * a4 * a5 ^ 4 * b4 * h ^ 32
    - (10628820 : F[X]) * a5 ^ 4 * b2 * h ^ 38
    - (177147000 : F[X]) * a0 * a3 * a5 ^ 3 * h ^ 42
    - (148803480 : F[X]) * a0 * a5 ^ 3 * b7 * h ^ 38
    - (177147000 : F[X]) * a1 * a2 * a5 ^ 3 * h ^ 42
    - (64953900 : F[X]) * a1 * a4 ^ 2 * a5 ^ 3 * h ^ 36
    + (623557440 : F[X]) * a1 * a4 * a5 ^ 3 * b8 * h ^ 32
    - (127545840 : F[X]) * a1 * a5 ^ 3 * b6 * h ^ 38
    - (129907800 : F[X]) * a2 * a3 * a4 * a5 ^ 3 * h ^ 36
    + (623557440 : F[X]) * a2 * a3 * a5 ^ 3 * b8 * h ^ 32
    + (545612760 : F[X]) * a2 * a4 * a5 ^ 3 * b7 * h ^ 32
    - (106288200 : F[X]) * a2 * a5 ^ 3 * b5 * h ^ 38
    - (21651300 : F[X]) * a3 ^ 3 * a5 ^ 3 * h ^ 36
    + (272806380 : F[X]) * a3 ^ 2 * a5 ^ 3 * b7 * h ^ 32
    + (707275800 : F[X]) * a3 * a4 ^ 3 * a5 ^ 3 * h ^ 30
    - (1454967360 : F[X]) * a3 * a4 ^ 2 * a5 ^ 3 * b8 * h ^ 26
    + (467668080 : F[X]) * a3 * a4 * a5 ^ 3 * b6 * h ^ 32
    - (85030560 : F[X]) * a3 * a5 ^ 3 * b4 * h ^ 38
    - (424365480 : F[X]) * a4 ^ 3 * a5 ^ 3 * b7 * h ^ 26
    + (194861700 : F[X]) * a4 ^ 2 * a5 ^ 3 * b5 * h ^ 32
    - (63772920 : F[X]) * a4 * a5 ^ 3 * b3 * h ^ 38
    + (7971615 : F[X]) * a5 ^ 3 * b1 * h ^ 44
    + (79716150 : F[X]) * a0 * a2 * a5 ^ 2 * h ^ 48
    + (212576400 : F[X]) * a0 * a4 ^ 2 * a5 ^ 2 * h ^ 42
    - (510183360 : F[X]) * a0 * a4 * a5 ^ 2 * b8 * h ^ 38
    + (143489070 : F[X]) * a0 * a5 ^ 2 * b6 * h ^ 44
    + (39858075 : F[X]) * a1 ^ 2 * a5 ^ 2 * h ^ 48
    + (425152800 : F[X]) * a1 * a3 * a4 * a5 ^ 2 * h ^ 42
    - (510183360 : F[X]) * a1 * a3 * a5 ^ 2 * b8 * h ^ 38
    - (446410440 : F[X]) * a1 * a4 * a5 ^ 2 * b7 * h ^ 38
    + (119574225 : F[X]) * a1 * a5 ^ 2 * b5 * h ^ 44
    + (212576400 : F[X]) * a2 ^ 2 * a4 * a5 ^ 2 * h ^ 42
    - (255091680 : F[X]) * a2 ^ 2 * a5 ^ 2 * b8 * h ^ 38
    + (212576400 : F[X]) * a2 * a3 ^ 2 * a5 ^ 2 * h ^ 42
    - (446410440 : F[X]) * a2 * a3 * a5 ^ 2 * b7 * h ^ 38
    - (649539000 : F[X]) * a2 * a4 ^ 3 * a5 ^ 2 * h ^ 36
    + (935336160 : F[X]) * a2 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 32
    - (382637520 : F[X]) * a2 * a4 * a5 ^ 2 * b6 * h ^ 38
    + (95659380 : F[X]) * a2 * a5 ^ 2 * b4 * h ^ 44
    - (974308500 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 ^ 2 * h ^ 36
    + (935336160 : F[X]) * a3 ^ 2 * a4 * a5 ^ 2 * b8 * h ^ 32
    - (191318760 : F[X]) * a3 ^ 2 * a5 ^ 2 * b6 * h ^ 38
    + (818419140 : F[X]) * a3 * a4 ^ 2 * a5 ^ 2 * b7 * h ^ 32
    - (318864600 : F[X]) * a3 * a4 * a5 ^ 2 * b5 * h ^ 38
    + (71744535 : F[X]) * a3 * a5 ^ 2 * b3 * h ^ 44
    + (242494560 : F[X]) * a4 ^ 5 * a5 ^ 2 * h ^ 30
    - (363741840 : F[X]) * a4 ^ 4 * a5 ^ 2 * b8 * h ^ 26
    + (233834040 : F[X]) * a4 ^ 3 * a5 ^ 2 * b6 * h ^ 32
    - (127545840 : F[X]) * a4 ^ 2 * a5 ^ 2 * b4 * h ^ 38
    + (47829690 : F[X]) * a4 * a5 ^ 2 * b2 * h ^ 44
    + (47829690 : F[X]) * a0 * a1 * a5 * h ^ 54
    - (558013050 : F[X]) * a0 * a3 * a4 * a5 * h ^ 48
    + (382637520 : F[X]) * a0 * a3 * a5 * b8 * h ^ 44
    + (334807830 : F[X]) * a0 * a4 * a5 * b7 * h ^ 44
    - (143489070 : F[X]) * a0 * a5 * b5 * h ^ 50
    - (558013050 : F[X]) * a1 * a2 * a4 * a5 * h ^ 48
    + (382637520 : F[X]) * a1 * a2 * a5 * b8 * h ^ 44
    - (279006525 : F[X]) * a1 * a3 ^ 2 * a5 * h ^ 48
    + (334807830 : F[X]) * a1 * a3 * a5 * b7 * h ^ 44
    + (460582200 : F[X]) * a1 * a4 ^ 3 * a5 * h ^ 42
    - (510183360 : F[X]) * a1 * a4 ^ 2 * a5 * b8 * h ^ 38
    + (286978140 : F[X]) * a1 * a4 * a5 * b6 * h ^ 44
    - (114791256 : F[X]) * a1 * a5 * b4 * h ^ 50
    - (279006525 : F[X]) * a2 ^ 2 * a3 * a5 * h ^ 48
    + (167403915 : F[X]) * a2 ^ 2 * a5 * b7 * h ^ 44
    + (1381746600 : F[X]) * a2 * a3 * a4 ^ 2 * a5 * h ^ 42
    - (1020366720 : F[X]) * a2 * a3 * a4 * a5 * b8 * h ^ 38
    + (286978140 : F[X]) * a2 * a3 * a5 * b6 * h ^ 44
    - (446410440 : F[X]) * a2 * a4 ^ 2 * a5 * b7 * h ^ 38
    + (239148450 : F[X]) * a2 * a4 * a5 * b5 * h ^ 44
    - (86093442 : F[X]) * a2 * a5 * b3 * h ^ 50
    + (460582200 : F[X]) * a3 ^ 3 * a4 * a5 * h ^ 42
    - (170061120 : F[X]) * a3 ^ 3 * a5 * b8 * h ^ 38
    - (446410440 : F[X]) * a3 ^ 2 * a4 * a5 * b7 * h ^ 38
    + (119574225 : F[X]) * a3 ^ 2 * a5 * b5 * h ^ 44
    - (617062050 : F[X]) * a3 * a4 ^ 4 * a5 * h ^ 36
    + (623557440 : F[X]) * a3 * a4 ^ 3 * a5 * b8 * h ^ 32
    - (382637520 : F[X]) * a3 * a4 ^ 2 * a5 * b6 * h ^ 38
    + (191318760 : F[X]) * a3 * a4 * a5 * b4 * h ^ 44
    - (57395628 : F[X]) * a3 * a5 * b2 * h ^ 50
    + (136403190 : F[X]) * a4 ^ 4 * a5 * b7 * h ^ 32
    - (106288200 : F[X]) * a4 ^ 3 * a5 * b5 * h ^ 38
    + (71744535 : F[X]) * a4 ^ 2 * a5 * b3 * h ^ 44
    - (28697814 : F[X]) * a4 * a5 * b1 * h ^ 50
    - (143489070 : F[X]) * a0 ^ 2 * h ^ 60
    + (478296900 : F[X]) * a0 * a2 * a4 * h ^ 54
    - (229582512 : F[X]) * a0 * a2 * b8 * h ^ 50
    + (239148450 : F[X]) * a0 * a3 ^ 2 * h ^ 54
    - (200884698 : F[X]) * a0 * a3 * b7 * h ^ 50
    - (212576400 : F[X]) * a0 * a4 ^ 3 * h ^ 48
    + (191318760 : F[X]) * a0 * a4 ^ 2 * b8 * h ^ 44
    - (172186884 : F[X]) * a0 * a4 * b6 * h ^ 50
    + (172186884 : F[X]) * a0 * b4 * h ^ 56
    + (239148450 : F[X]) * a1 ^ 2 * a4 * h ^ 54
    - (114791256 : F[X]) * a1 ^ 2 * b8 * h ^ 50
    + (478296900 : F[X]) * a1 * a2 * a3 * h ^ 54
    - (200884698 : F[X]) * a1 * a2 * b7 * h ^ 50
    - (637729200 : F[X]) * a1 * a3 * a4 ^ 2 * h ^ 48
    + (382637520 : F[X]) * a1 * a3 * a4 * b8 * h ^ 44
    - (172186884 : F[X]) * a1 * a3 * b6 * h ^ 50
    + (167403915 : F[X]) * a1 * a4 ^ 2 * b7 * h ^ 44
    - (143489070 : F[X]) * a1 * a4 * b5 * h ^ 50
    + (129140163 : F[X]) * a1 * b3 * h ^ 56
    + (79716150 : F[X]) * a2 ^ 3 * h ^ 54
    - (318864600 : F[X]) * a2 ^ 2 * a4 ^ 2 * h ^ 48
    + (191318760 : F[X]) * a2 ^ 2 * a4 * b8 * h ^ 44
    - (86093442 : F[X]) * a2 ^ 2 * b6 * h ^ 50
    - (637729200 : F[X]) * a2 * a3 ^ 2 * a4 * h ^ 48
    + (191318760 : F[X]) * a2 * a3 ^ 2 * b8 * h ^ 44
    + (334807830 : F[X]) * a2 * a3 * a4 * b7 * h ^ 44
    - (143489070 : F[X]) * a2 * a3 * b5 * h ^ 50
    + (194861700 : F[X]) * a2 * a4 ^ 4 * h ^ 42
    - (170061120 : F[X]) * a2 * a4 ^ 3 * b8 * h ^ 38
    + (143489070 : F[X]) * a2 * a4 ^ 2 * b6 * h ^ 44
    - (114791256 : F[X]) * a2 * a4 * b4 * h ^ 50
    + (86093442 : F[X]) * a2 * b2 * h ^ 56
    - (53144100 : F[X]) * a3 ^ 4 * h ^ 48
    + (55801305 : F[X]) * a3 ^ 3 * b7 * h ^ 44
    + (389723400 : F[X]) * a3 ^ 2 * a4 ^ 3 * h ^ 42
    - (255091680 : F[X]) * a3 ^ 2 * a4 ^ 2 * b8 * h ^ 38
    + (143489070 : F[X]) * a3 ^ 2 * a4 * b6 * h ^ 44
    - (57395628 : F[X]) * a3 ^ 2 * b4 * h ^ 50
    - (148803480 : F[X]) * a3 * a4 ^ 3 * b7 * h ^ 38
    + (119574225 : F[X]) * a3 * a4 ^ 2 * b5 * h ^ 44
    - (86093442 : F[X]) * a3 * a4 * b3 * h ^ 50
    + (43046721 : F[X]) * a3 * b1 * h ^ 56
    - (30311820 : F[X]) * a4 ^ 6 * h ^ 36
    + (31177872 : F[X]) * a4 ^ 5 * b8 * h ^ 32
    - (31886460 : F[X]) * a4 ^ 4 * b6 * h ^ 38
    + (31886460 : F[X]) * a4 ^ 3 * b4 * h ^ 44
    - (28697814 : F[X]) * a4 ^ 2 * b2 * h ^ 50 := by
  simp [localClearedTwelfthDefect610, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk01, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk02, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk03, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk04, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk05, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk06, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk07, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk08, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk09, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk10, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk11, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk12, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk13, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk14, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk15, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk16, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk17, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk18, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk19, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk20, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk21, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk22, fable610eleventhSpeedT_localClearedTwelfthDefect610_chunk23, map_zero]



end Depression610Twelfth

end ScaleZeroEleventhDefect610
end Max11DegreeRoutes
end
