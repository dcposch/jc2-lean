import Fable610ScaleZeroEleventhDefectScratch

/-! # Scale-zero twelfth cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Fable610ScaleZeroEleventhDefectScratch` on the constant
core `H = (C t)²`.  The eleventh packet already forces the discriminator
`N`, the weight-fifty-five defect `κ`, and the weight-sixty defect `λ`
to ground constants, including the exact selectors
`3134566563840 p₀ q₅ h⁵⁰` and `172186884 p₀ q₄ h⁵⁶`.  This file
consumes the next unused Keller coefficient, the degree-`2` Jacobian
row

```
(p₂)' (1 q₁) + (p₁)' (2 q₂) + (p₀)' (3 q₃)
  - (3 p₃) q₀' - (2 p₂) q₁' - (1 p₁) q₂' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is `3 U E' + 2 V D' + W C' - D V' - 2 C W' - 3 B X' = 0`.
The derivative `X'` is eliminated through the degree-`5` row and `W'`
through the degree-`6` row.  Unlike the higher rows, the reduced
`1`-form of the degree-`2` row is not exact on its own: its exterior
derivative is `-3 dA ∧ dκ`, so the already-consumed degree-`4` row
re-enters with the polynomial coefficient `-(1/12) A`, and the first
integral `μ` obeys `d μ = (1/6)·row₂ - (1/12)·A·row₄`.  The `μ`
formula, its weight-sixty-five clearing by `12582912 h⁶⁵`, the solved
derivative forms, and the aligned `227`-monomial specialization were
derived and cross-checked independently (closedness of the corrected
`1`-form, the identity `d μ = (1/6) row₂ - (1/12) A row₄`, and a
rational end-to-end evaluation of the cleared `285`-monomial
polynomial).  The derivation-in-zero reduction keeps the sub-residuals
opaque so the tower hypotheses fire, and supplies the complete
constant-derivative kill set from `d (1/2) = 0` through
`d (77/15552) = 0` and `d (A⁶)`, `d (B⁴)`, `d (C³)`.

The degree-`5` iota first integral, the exact `18 q₀ h⁵⁰` residual, the
weight-fifty-five kappa selector `3134566563840 p₀ q₅ h⁵⁰`, and the
weight-sixty lambda selector `172186884 p₀ q₄ h⁵⁶` are preserved and
not cleared to zero.  No total-degree or twice-prime theorem is used.
A constant scale has no finite root, so no root-jet packet exists at
this scale.  Both the vanishing and the nonzero constant branches of
`λ` and of the weight-sixty and weight-sixty-five defects are kept.
The packet does not close the leaf: unused Jacobian coefficients start
at degree `1`.
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

section ScaleZeroTwelfthDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/


set_option maxHeartbeats 64000000 in
/-- The thirteenth row below the leading weighted-Wronskian row for
outer degrees `(6,10)`.  Unused Jacobian coefficients of the eleventh
packet start at degree `2`. -/
theorem scaleZeroRaw_thirteenthCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 2).derivative * q.coeff 1 +
        (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : K)) -
      ((p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 0).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 1).derivative +
        p.coeff 1 * (q.coeff 2).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 2) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (2 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 2 :
      Finset (ℕ × ℕ)) =
      ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)) := by decide
  rw [hanti] at hcoeff
  norm_num [hp, hq, Polynomial.coeff_eq_zero_of_natDegree_lt] at hcoeff ⊢
  have hC2 : Polynomial.C (2 : K) = (2 : K[X]) :=
    Polynomial.C_eq_natCast 2
  have hC3 : Polynomial.C (3 : K) = (3 : K[X]) :=
    Polynomial.C_eq_natCast 3
  rw [hC2, hC3]
  linear_combination hcoeff

set_option maxHeartbeats 64000000 in
/-- Source-facing degree-`2` Jacobian row of a normalized scale-zero
`(6,10)` pair. -/
theorem normalized610ScaleZero_thirteenthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 2).derivative * q.coeff 1 +
        (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : k)) -
      ((p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 0).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 1).derivative +
        p.coeff 1 * (q.coeff 2).derivative) =
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
    scaleZeroRaw_thirteenthCoefficientJacobianRow_610 hp hq hjac

set_option maxHeartbeats 64000000 in
/-- At scale zero the common core is constant; the degree-`2` row has no
`p₆'`, `p₅'`, `q₁₀'`, or `q₉'` term, so it collapses to the same literal
row. -/
theorem scaleZero_thirteenthCoefficientJacobianRow_610
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 2).derivative * q.coeff 1 +
        (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : k)) -
      ((p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 0).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 1).derivative +
        p.coeff 1 * (q.coeff 2).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp6der : (p.coeff 6).derivative = 0 := by
    rw [hp6, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := scaleZeroRaw_thirteenthCoefficientJacobianRow_610 hp hq hjac
  simpa [hp6der, hq10der] using hrow

set_option maxHeartbeats 64000000 in
/-- Source-facing scale-zero collapse of the degree-`2` row. -/
theorem normalized610ScaleZero_thirteenthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 2).derivative * q.coeff 1 +
        (p.coeff 1).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 0).derivative * (q.coeff 3 * Polynomial.C (3 : k)) -
      ((p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 0).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 1).derivative +
        p.coeff 1 * (q.coeff 2).derivative) =
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
    scaleZero_thirteenthCoefficientJacobianRow_610 hp hq hjac hHdegree
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)

/-! ## Weight-sixty-five cleared defect after a square root of the core -/

section Depression610Thirteenth

variable {F : Type*} [Field F] [CharZero F]


set_option maxHeartbeats 64000000 in
/-- First residual of the degree-`2` row, with `X'` eliminated through
the degree-`5` row, `W'` through the degree-`6` row, and the
already-consumed degree-`4` row re-entering with coefficient
`-(1/12) A`, so that `d μ = (1/6) row₂ - (1/12) A row₄` on the second-
through ninth-face integrals. -/
def muResidual610
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  -(1 / 24 : F) * A ^ 2 * thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0
  + (1 / 6 : F) * C0 * thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0
  - (1 / 6 : F) * A * B * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0
  + (1 / 3 : F) * D0 * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0
  + (1 / 24 : F) * A ^ 3 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0
  - (1 / 6 : F) * A * C0 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0
  - (1 / 8 : F) * B ^ 2 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0
  + (1 / 2 : F) * E0 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0
  + (1 / 9 : F) * A ^ 2 * B * epsilonResidual610 L A B C0 D0 E0 P Q R T0
  - (1 / 9 : F) * A * D0 * epsilonResidual610 L A B C0 D0 E0 P Q R T0
  - (2 / 9 : F) * B * C0 * epsilonResidual610 L A B C0 D0 E0 P Q R T0
  - (35 / 3456 : F) * A ^ 4 * deltaResidual610 L A B C0 D0 P Q S0
  + (25 / 432 : F) * A ^ 2 * C0 * deltaResidual610 L A B C0 D0 P Q S0
  + (5 / 72 : F) * A * B ^ 2 * deltaResidual610 L A B C0 D0 P Q S0
  - (5 / 36 : F) * B * D0 * deltaResidual610 L A B C0 D0 P Q S0
  - (5 / 72 : F) * C0 ^ 2 * deltaResidual610 L A B C0 D0 P Q S0
  - (10 / 243 : F) * A ^ 4 * B * alphaResidual610 A P
  + (14 / 243 : F) * A ^ 3 * D0 * alphaResidual610 A P
  + (16 / 81 : F) * A ^ 2 * B * C0 * alphaResidual610 A P
  + (2 / 27 : F) * A * B ^ 3 * alphaResidual610 A P
  - (2 / 9 : F) * A * B * E0 * alphaResidual610 A P
  - (2 / 9 : F) * A * C0 * D0 * alphaResidual610 A P
  - (4 / 27 : F) * B ^ 2 * D0 * alphaResidual610 A P
  - (4 / 27 : F) * B * C0 ^ 2 * alphaResidual610 A P
  + (4 / 9 : F) * D0 * E0 * alphaResidual610 A P
  - (77 / 15552 : F) * A ^ 5 * betaResidual610 L A B Q
  + (35 / 972 : F) * A ^ 3 * C0 * betaResidual610 L A B Q
  + (35 / 576 : F) * A ^ 2 * B ^ 2 * betaResidual610 L A B Q
  - (7 / 144 : F) * A ^ 2 * E0 * betaResidual610 L A B Q
  - (7 / 54 : F) * A * B * D0 * betaResidual610 L A B Q
  - (7 / 108 : F) * A * C0 ^ 2 * betaResidual610 L A B Q
  - (35 / 432 : F) * B ^ 2 * C0 * betaResidual610 L A B Q
  + (7 / 36 : F) * C0 * E0 * betaResidual610 L A B Q
  + (7 / 72 : F) * D0 ^ 2 * betaResidual610 L A B Q
  + (5 / 1024 : F) * L * A ^ 6
  - (11 / 256 : F) * L * A ^ 4 * C0
  - (3 / 32 : F) * L * A ^ 3 * B ^ 2
  + (1 / 16 : F) * L * A ^ 3 * E0
  + (7 / 32 : F) * L * A ^ 2 * B * D0
  + (7 / 64 : F) * L * A ^ 2 * C0 ^ 2
  + (1 / 4 : F) * L * A * B ^ 2 * C0
  - (1 / 4 : F) * L * A * C0 * E0
  - (1 / 8 : F) * L * A * D0 ^ 2
  + (3 / 128 : F) * L * B ^ 4
  - (3 / 16 : F) * L * B ^ 2 * E0
  - (3 / 8 : F) * L * B * C0 * D0
  - (1 / 16 : F) * L * C0 ^ 3
  + (3 / 8 : F) * L * E0 ^ 2
  + (35 / 1458 : F) * A ^ 5 * B
  - (25 / 729 : F) * A ^ 4 * D0
  - (110 / 729 : F) * A ^ 3 * B * C0
  - (20 / 243 : F) * A ^ 2 * B ^ 3
  + (5 / 27 : F) * A ^ 2 * B * E0
  + (5 / 27 : F) * A ^ 2 * C0 * D0
  + (35 / 162 : F) * A * B ^ 2 * D0
  + (35 / 162 : F) * A * B * C0 ^ 2
  - (5 / 27 : F) * A * D0 * E0
  + (20 / 243 : F) * B ^ 3 * C0
  - (10 / 27 : F) * B * C0 * E0
  - (5 / 27 : F) * B * D0 ^ 2
  - (5 / 27 : F) * C0 ^ 2 * D0
set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 10. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk01
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    -(180880 : F[X]) * a5 ^ 13
    + (88179 : F[X]) * a5 ^ 12 * h ^ 5 * Polynomial.C lambda
    + (2015520 : F[X]) * a4 * a5 ^ 11 * h ^ 6
    + (268736 : F[X]) * a5 ^ 11 * b8 * h ^ 2
    - (2139280 : F[X]) * a3 * a5 ^ 10 * h ^ 12
    - (1108536 : F[X]) * a4 * a5 ^ 10 * h ^ 11 * Polynomial.C lambda
    - (272272 : F[X]) * a5 ^ 10 * b7 * h ^ 8
    + (2288000 : F[X]) * a2 * a5 ^ 9 * h ^ 18
    + (1166880 : F[X]) * a3 * a5 ^ 9 * h ^ 17 * Polynomial.C lambda
    - (7779200 : F[X]) * a4 ^ 2 * a5 ^ 9 * h ^ 12

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 20. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk02 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (3111680 : F[X]) * a4 * a5 ^ 9 * b8 * h ^ 8
    + (274560 : F[X]) * a5 ^ 9 * b6 * h ^ 14
    - (2471040 : F[X]) * a1 * a5 ^ 8 * h ^ 24
    - (1235520 : F[X]) * a2 * a5 ^ 8 * h ^ 23 * Polynomial.C lambda
    + (14414400 : F[X]) * a3 * a4 * a5 ^ 8 * h ^ 18
    + (3294720 : F[X]) * a3 * a5 ^ 8 * b8 * h ^ 14
    + (5250960 : F[X]) * a4 ^ 2 * a5 ^ 8 * h ^ 17 * Polynomial.C lambda
    + (2882880 : F[X]) * a4 * a5 ^ 8 * b7 * h ^ 14
    - (274560 : F[X]) * a5 ^ 8 * b5 * h ^ 20
    + (2703360 : F[X]) * a0 * a5 ^ 7 * h ^ 30

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 30. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk03 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (1317888 : F[X]) * a1 * a5 ^ 7 * h ^ 29 * Polynomial.C lambda
    - (13178880 : F[X]) * a2 * a4 * a5 ^ 7 * h ^ 24
    - (3514368 : F[X]) * a2 * a5 ^ 7 * b8 * h ^ 20
    - (6589440 : F[X]) * a3 ^ 2 * a5 ^ 7 * h ^ 24
    - (9884160 : F[X]) * a3 * a4 * a5 ^ 7 * h ^ 23 * Polynomial.C lambda
    - (3075072 : F[X]) * a3 * a5 ^ 7 * b7 * h ^ 20
    + (10982400 : F[X]) * a4 ^ 3 * a5 ^ 7 * h ^ 18
    + (13178880 : F[X]) * a4 ^ 2 * a5 ^ 7 * b8 * h ^ 14
    - (2635776 : F[X]) * a4 * a5 ^ 7 * b6 * h ^ 20
    + (270336 : F[X]) * a5 ^ 7 * b4 * h ^ 26

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 40. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk04 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (1419264 : F[X]) * a0 * a5 ^ 6 * h ^ 35 * Polynomial.C lambda
    + (11827200 : F[X]) * a1 * a4 * a5 ^ 6 * h ^ 30
    + (3784704 : F[X]) * a1 * a5 ^ 6 * b8 * h ^ 26
    + (11827200 : F[X]) * a2 * a3 * a5 ^ 6 * h ^ 30
    + (9225216 : F[X]) * a2 * a4 * a5 ^ 6 * h ^ 29 * Polynomial.C lambda
    + (3311616 : F[X]) * a2 * a5 ^ 6 * b7 * h ^ 26
    + (4612608 : F[X]) * a3 ^ 2 * a5 ^ 6 * h ^ 29 * Polynomial.C lambda
    - (23063040 : F[X]) * a3 * a4 ^ 2 * a5 ^ 6 * h ^ 24
    - (24600576 : F[X]) * a3 * a4 * a5 ^ 6 * b8 * h ^ 20
    + (2838528 : F[X]) * a3 * a5 ^ 6 * b6 * h ^ 26

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 50. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk05 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (11531520 : F[X]) * a4 ^ 3 * a5 ^ 6 * h ^ 23 * Polynomial.C lambda
    - (10762752 : F[X]) * a4 ^ 2 * a5 ^ 6 * b7 * h ^ 20
    + (2365440 : F[X]) * a4 * a5 ^ 6 * b5 * h ^ 26
    - (258048 : F[X]) * a5 ^ 6 * b3 * h ^ 32
    - (10321920 : F[X]) * a0 * a4 * a5 ^ 5 * h ^ 36
    - (4128768 : F[X]) * a0 * a5 ^ 5 * b8 * h ^ 32
    - (10321920 : F[X]) * a1 * a3 * a5 ^ 5 * h ^ 36
    - (8515584 : F[X]) * a1 * a4 * a5 ^ 5 * h ^ 35 * Polynomial.C lambda
    - (3612672 : F[X]) * a1 * a5 ^ 5 * b7 * h ^ 32
    - (5160960 : F[X]) * a2 ^ 2 * a5 ^ 5 * h ^ 36

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 60. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk06 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (8515584 : F[X]) * a2 * a3 * a5 ^ 5 * h ^ 35 * Polynomial.C lambda
    + (14192640 : F[X]) * a2 * a4 ^ 2 * a5 ^ 5 * h ^ 30
    + (22708224 : F[X]) * a2 * a4 * a5 ^ 5 * b8 * h ^ 26
    - (3096576 : F[X]) * a2 * a5 ^ 5 * b6 * h ^ 32
    + (14192640 : F[X]) * a3 ^ 2 * a4 * a5 ^ 5 * h ^ 30
    + (11354112 : F[X]) * a3 ^ 2 * a5 ^ 5 * b8 * h ^ 26
    + (27675648 : F[X]) * a3 * a4 ^ 2 * a5 ^ 5 * h ^ 29 * Polynomial.C lambda
    + (19869696 : F[X]) * a3 * a4 * a5 ^ 5 * b7 * h ^ 26
    - (2580480 : F[X]) * a3 * a5 ^ 5 * b5 * h ^ 32
    - (24600576 : F[X]) * a4 ^ 3 * a5 ^ 5 * b8 * h ^ 20

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 70. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk07 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (8515584 : F[X]) * a4 ^ 2 * a5 ^ 5 * b6 * h ^ 26
    - (2064384 : F[X]) * a4 * a5 ^ 5 * b4 * h ^ 32
    + (229376 : F[X]) * a5 ^ 5 * b2 * h ^ 38
    + (8601600 : F[X]) * a0 * a3 * a5 ^ 4 * h ^ 42
    + (7741440 : F[X]) * a0 * a4 * a5 ^ 4 * h ^ 41 * Polynomial.C lambda
    + (4014080 : F[X]) * a0 * a5 ^ 4 * b7 * h ^ 38
    + (8601600 : F[X]) * a1 * a2 * a5 ^ 4 * h ^ 42
    + (7741440 : F[X]) * a1 * a3 * a5 ^ 4 * h ^ 41 * Polynomial.C lambda
    - (6451200 : F[X]) * a1 * a4 ^ 2 * a5 ^ 4 * h ^ 36
    - (20643840 : F[X]) * a1 * a4 * a5 ^ 4 * b8 * h ^ 32

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 80. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk08 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (3440640 : F[X]) * a1 * a5 ^ 4 * b6 * h ^ 38
    + (3870720 : F[X]) * a2 ^ 2 * a5 ^ 4 * h ^ 41 * Polynomial.C lambda
    - (12902400 : F[X]) * a2 * a3 * a4 * a5 ^ 4 * h ^ 36
    - (20643840 : F[X]) * a2 * a3 * a5 ^ 4 * b8 * h ^ 32
    - (21288960 : F[X]) * a2 * a4 ^ 2 * a5 ^ 4 * h ^ 35 * Polynomial.C lambda
    - (18063360 : F[X]) * a2 * a4 * a5 ^ 4 * b7 * h ^ 32
    + (2867200 : F[X]) * a2 * a5 ^ 4 * b5 * h ^ 38
    - (2150400 : F[X]) * a3 ^ 3 * a5 ^ 4 * h ^ 36
    - (21288960 : F[X]) * a3 ^ 2 * a4 * a5 ^ 4 * h ^ 35 * Polynomial.C lambda
    - (9031680 : F[X]) * a3 ^ 2 * a5 ^ 4 * b7 * h ^ 32

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 90. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk09 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (11827200 : F[X]) * a3 * a4 ^ 3 * a5 ^ 4 * h ^ 30
    + (56770560 : F[X]) * a3 * a4 ^ 2 * a5 ^ 4 * b8 * h ^ 26
    - (15482880 : F[X]) * a3 * a4 * a5 ^ 4 * b6 * h ^ 32
    + (2293760 : F[X]) * a3 * a5 ^ 4 * b4 * h ^ 38
    + (11531520 : F[X]) * a4 ^ 4 * a5 ^ 4 * h ^ 29 * Polynomial.C lambda
    + (16558080 : F[X]) * a4 ^ 3 * a5 ^ 4 * b7 * h ^ 26
    - (6451200 : F[X]) * a4 ^ 2 * a5 ^ 4 * b5 * h ^ 32
    + (1720320 : F[X]) * a4 * a5 ^ 4 * b3 * h ^ 38
    - (163840 : F[X]) * a5 ^ 4 * b1 * h ^ 44
    - (6553600 : F[X]) * a0 * a2 * a5 ^ 3 * h ^ 48

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 100. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk10 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (6881280 : F[X]) * a0 * a3 * a5 ^ 3 * h ^ 47 * Polynomial.C lambda
    + (18350080 : F[X]) * a0 * a4 * a5 ^ 3 * b8 * h ^ 38
    - (3932160 : F[X]) * a0 * a5 ^ 3 * b6 * h ^ 44
    - (3276800 : F[X]) * a1 ^ 2 * a5 ^ 3 * h ^ 48
    - (6881280 : F[X]) * a1 * a2 * a5 ^ 3 * h ^ 47 * Polynomial.C lambda
    + (18350080 : F[X]) * a1 * a3 * a5 ^ 3 * b8 * h ^ 38
    + (15482880 : F[X]) * a1 * a4 ^ 2 * a5 ^ 3 * h ^ 41 * Polynomial.C lambda
    + (16056320 : F[X]) * a1 * a4 * a5 ^ 3 * b7 * h ^ 38
    - (3276800 : F[X]) * a1 * a5 ^ 3 * b5 * h ^ 44
    + (9175040 : F[X]) * a2 ^ 2 * a5 ^ 3 * b8 * h ^ 38

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 110. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk11 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (30965760 : F[X]) * a2 * a3 * a4 * a5 ^ 3 * h ^ 41 * Polynomial.C lambda
    + (16056320 : F[X]) * a2 * a3 * a5 ^ 3 * b7 * h ^ 38
    + (17203200 : F[X]) * a2 * a4 ^ 3 * a5 ^ 3 * h ^ 36
    - (41287680 : F[X]) * a2 * a4 ^ 2 * a5 ^ 3 * b8 * h ^ 32
    + (13762560 : F[X]) * a2 * a4 * a5 ^ 3 * b6 * h ^ 38
    - (2621440 : F[X]) * a2 * a5 ^ 3 * b4 * h ^ 44
    + (5160960 : F[X]) * a3 ^ 3 * a5 ^ 3 * h ^ 41 * Polynomial.C lambda
    + (25804800 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 ^ 3 * h ^ 36
    - (41287680 : F[X]) * a3 ^ 2 * a4 * a5 ^ 3 * b8 * h ^ 32
    + (6881280 : F[X]) * a3 ^ 2 * a5 ^ 3 * b6 * h ^ 38

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 120. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk12 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (28385280 : F[X]) * a3 * a4 ^ 3 * a5 ^ 3 * h ^ 35 * Polynomial.C lambda
    - (36126720 : F[X]) * a3 * a4 ^ 2 * a5 ^ 3 * b7 * h ^ 32
    + (11468800 : F[X]) * a3 * a4 * a5 ^ 3 * b5 * h ^ 38
    - (1966080 : F[X]) * a3 * a5 ^ 3 * b3 * h ^ 44
    - (9461760 : F[X]) * a4 ^ 5 * a5 ^ 3 * h ^ 30
    + (18923520 : F[X]) * a4 ^ 4 * a5 ^ 3 * b8 * h ^ 26
    - (10321920 : F[X]) * a4 ^ 3 * a5 ^ 3 * b6 * h ^ 32
    + (4587520 : F[X]) * a4 ^ 2 * a5 ^ 3 * b4 * h ^ 38
    - (1310720 : F[X]) * a4 * a5 ^ 3 * b2 * h ^ 44
    + (3932160 : F[X]) * a0 * a1 * a5 ^ 2 * h ^ 54

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 130. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk13 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (5898240 : F[X]) * a0 * a2 * a5 ^ 2 * h ^ 53 * Polynomial.C lambda
    + (9830400 : F[X]) * a0 * a3 * a4 * a5 ^ 2 * h ^ 48
    - (15728640 : F[X]) * a0 * a3 * a5 ^ 2 * b8 * h ^ 44
    - (10321920 : F[X]) * a0 * a4 ^ 2 * a5 ^ 2 * h ^ 47 * Polynomial.C lambda
    - (13762560 : F[X]) * a0 * a4 * a5 ^ 2 * b7 * h ^ 44
    + (3932160 : F[X]) * a0 * a5 ^ 2 * b5 * h ^ 50
    + (2949120 : F[X]) * a1 ^ 2 * a5 ^ 2 * h ^ 53 * Polynomial.C lambda
    + (9830400 : F[X]) * a1 * a2 * a4 * a5 ^ 2 * h ^ 48
    - (15728640 : F[X]) * a1 * a2 * a5 ^ 2 * b8 * h ^ 44
    + (4915200 : F[X]) * a1 * a3 ^ 2 * a5 ^ 2 * h ^ 48

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 140. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk14 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (20643840 : F[X]) * a1 * a3 * a4 * a5 ^ 2 * h ^ 47 * Polynomial.C lambda
    - (13762560 : F[X]) * a1 * a3 * a5 ^ 2 * b7 * h ^ 44
    - (17203200 : F[X]) * a1 * a4 ^ 3 * a5 ^ 2 * h ^ 42
    + (27525120 : F[X]) * a1 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 38
    - (11796480 : F[X]) * a1 * a4 * a5 ^ 2 * b6 * h ^ 44
    + (3145728 : F[X]) * a1 * a5 ^ 2 * b4 * h ^ 50
    + (4915200 : F[X]) * a2 ^ 2 * a3 * a5 ^ 2 * h ^ 48
    - (10321920 : F[X]) * a2 ^ 2 * a4 * a5 ^ 2 * h ^ 47 * Polynomial.C lambda
    - (6881280 : F[X]) * a2 ^ 2 * a5 ^ 2 * b7 * h ^ 44
    - (10321920 : F[X]) * a2 * a3 ^ 2 * a5 ^ 2 * h ^ 47 * Polynomial.C lambda

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 150. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk15 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (51609600 : F[X]) * a2 * a3 * a4 ^ 2 * a5 ^ 2 * h ^ 42
    + (55050240 : F[X]) * a2 * a3 * a4 * a5 ^ 2 * b8 * h ^ 38
    - (11796480 : F[X]) * a2 * a3 * a5 ^ 2 * b6 * h ^ 44
    + (15482880 : F[X]) * a2 * a4 ^ 3 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda
    + (24084480 : F[X]) * a2 * a4 ^ 2 * a5 ^ 2 * b7 * h ^ 38
    - (9830400 : F[X]) * a2 * a4 * a5 ^ 2 * b5 * h ^ 44
    + (2359296 : F[X]) * a2 * a5 ^ 2 * b3 * h ^ 50
    - (17203200 : F[X]) * a3 ^ 3 * a4 * a5 ^ 2 * h ^ 42
    + (9175040 : F[X]) * a3 ^ 3 * a5 ^ 2 * b8 * h ^ 38
    + (23224320 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 160. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk16 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (24084480 : F[X]) * a3 ^ 2 * a4 * a5 ^ 2 * b7 * h ^ 38
    - (4915200 : F[X]) * a3 ^ 2 * a5 ^ 2 * b5 * h ^ 44
    + (32256000 : F[X]) * a3 * a4 ^ 4 * a5 ^ 2 * h ^ 36
    - (41287680 : F[X]) * a3 * a4 ^ 3 * a5 ^ 2 * b8 * h ^ 32
    + (20643840 : F[X]) * a3 * a4 ^ 2 * a5 ^ 2 * b6 * h ^ 38
    - (7864320 : F[X]) * a3 * a4 * a5 ^ 2 * b4 * h ^ 44
    + (1572864 : F[X]) * a3 * a5 ^ 2 * b2 * h ^ 50
    - (4257792 : F[X]) * a4 ^ 5 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    - (9031680 : F[X]) * a4 ^ 4 * a5 ^ 2 * b7 * h ^ 32
    + (5734400 : F[X]) * a4 ^ 3 * a5 ^ 2 * b5 * h ^ 38

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 170. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk17 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (2949120 : F[X]) * a4 ^ 2 * a5 ^ 2 * b3 * h ^ 44
    + (786432 : F[X]) * a4 * a5 ^ 2 * b1 * h ^ 50
    - (4718592 : F[X]) * a0 * a1 * a5 * h ^ 59 * Polynomial.C lambda
    - (15728640 : F[X]) * a0 * a2 * a4 * a5 * h ^ 54
    + (12582912 : F[X]) * a0 * a2 * a5 * b8 * h ^ 50
    - (7864320 : F[X]) * a0 * a3 ^ 2 * a5 * h ^ 54
    + (11796480 : F[X]) * a0 * a3 * a4 * a5 * h ^ 53 * Polynomial.C lambda
    + (11010048 : F[X]) * a0 * a3 * a5 * b7 * h ^ 50
    + (13107200 : F[X]) * a0 * a4 ^ 3 * a5 * h ^ 48
    - (15728640 : F[X]) * a0 * a4 ^ 2 * a5 * b8 * h ^ 44

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 180. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk18 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (9437184 : F[X]) * a0 * a4 * a5 * b6 * h ^ 50
    - (4194304 : F[X]) * a0 * a5 * b4 * h ^ 56
    - (7864320 : F[X]) * a1 ^ 2 * a4 * a5 * h ^ 54
    + (6291456 : F[X]) * a1 ^ 2 * a5 * b8 * h ^ 50
    - (15728640 : F[X]) * a1 * a2 * a3 * a5 * h ^ 54
    + (11796480 : F[X]) * a1 * a2 * a4 * a5 * h ^ 53 * Polynomial.C lambda
    + (11010048 : F[X]) * a1 * a2 * a5 * b7 * h ^ 50
    + (5898240 : F[X]) * a1 * a3 ^ 2 * a5 * h ^ 53 * Polynomial.C lambda
    + (39321600 : F[X]) * a1 * a3 * a4 ^ 2 * a5 * h ^ 48
    - (31457280 : F[X]) * a1 * a3 * a4 * a5 * b8 * h ^ 44

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 190. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk19 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (9437184 : F[X]) * a1 * a3 * a5 * b6 * h ^ 50
    - (6881280 : F[X]) * a1 * a4 ^ 3 * a5 * h ^ 47 * Polynomial.C lambda
    - (13762560 : F[X]) * a1 * a4 ^ 2 * a5 * b7 * h ^ 44
    + (7864320 : F[X]) * a1 * a4 * a5 * b5 * h ^ 50
    - (3145728 : F[X]) * a1 * a5 * b3 * h ^ 56
    - (2621440 : F[X]) * a2 ^ 3 * a5 * h ^ 54
    + (5898240 : F[X]) * a2 ^ 2 * a3 * a5 * h ^ 53 * Polynomial.C lambda
    + (19660800 : F[X]) * a2 ^ 2 * a4 ^ 2 * a5 * h ^ 48
    - (15728640 : F[X]) * a2 ^ 2 * a4 * a5 * b8 * h ^ 44
    + (4718592 : F[X]) * a2 ^ 2 * a5 * b6 * h ^ 50

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 200. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk20 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (39321600 : F[X]) * a2 * a3 ^ 2 * a4 * a5 * h ^ 48
    - (15728640 : F[X]) * a2 * a3 ^ 2 * a5 * b8 * h ^ 44
    - (20643840 : F[X]) * a2 * a3 * a4 ^ 2 * a5 * h ^ 47 * Polynomial.C lambda
    - (27525120 : F[X]) * a2 * a3 * a4 * a5 * b7 * h ^ 44
    + (7864320 : F[X]) * a2 * a3 * a5 * b5 * h ^ 50
    - (17203200 : F[X]) * a2 * a4 ^ 4 * a5 * h ^ 42
    + (18350080 : F[X]) * a2 * a4 ^ 3 * a5 * b8 * h ^ 38
    - (11796480 : F[X]) * a2 * a4 ^ 2 * a5 * b6 * h ^ 44
    + (6291456 : F[X]) * a2 * a4 * a5 * b4 * h ^ 50
    - (2097152 : F[X]) * a2 * a5 * b2 * h ^ 56

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 210. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk21 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (3276800 : F[X]) * a3 ^ 4 * a5 * h ^ 48
    - (6881280 : F[X]) * a3 ^ 3 * a4 * a5 * h ^ 47 * Polynomial.C lambda
    - (4587520 : F[X]) * a3 ^ 3 * a5 * b7 * h ^ 44
    - (34406400 : F[X]) * a3 ^ 2 * a4 ^ 3 * a5 * h ^ 42
    + (27525120 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 * b8 * h ^ 38
    - (11796480 : F[X]) * a3 ^ 2 * a4 * a5 * b6 * h ^ 44
    + (3145728 : F[X]) * a3 ^ 2 * a5 * b4 * h ^ 50
    + (7741440 : F[X]) * a3 * a4 ^ 4 * a5 * h ^ 41 * Polynomial.C lambda
    + (16056320 : F[X]) * a3 * a4 ^ 3 * a5 * b7 * h ^ 38
    - (9830400 : F[X]) * a3 * a4 ^ 2 * a5 * b5 * h ^ 44

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 220. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk22 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (4718592 : F[X]) * a3 * a4 * a5 * b3 * h ^ 50
    - (1048576 : F[X]) * a3 * a5 * b1 * h ^ 56
    + (3440640 : F[X]) * a4 ^ 6 * a5 * h ^ 36
    - (4128768 : F[X]) * a4 ^ 5 * a5 * b8 * h ^ 32
    + (3440640 : F[X]) * a4 ^ 4 * a5 * b6 * h ^ 38
    - (2621440 : F[X]) * a4 ^ 3 * a5 * b4 * h ^ 44
    + (1572864 : F[X]) * a4 ^ 2 * a5 * b2 * h ^ 50
    + (1572864 : F[X]) * a0 ^ 2 * h ^ 65 * Polynomial.C lambda
    + (15728640 : F[X]) * a0 * a1 * a4 * h ^ 60
    - (8388608 : F[X]) * a0 * a1 * b8 * h ^ 56

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 230. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk23 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (15728640 : F[X]) * a0 * a2 * a3 * h ^ 60
    - (4718592 : F[X]) * a0 * a2 * a4 * h ^ 59 * Polynomial.C lambda
    - (7340032 : F[X]) * a0 * a2 * b7 * h ^ 56
    - (2359296 : F[X]) * a0 * a3 ^ 2 * h ^ 59 * Polynomial.C lambda
    - (19660800 : F[X]) * a0 * a3 * a4 ^ 2 * h ^ 54
    + (12582912 : F[X]) * a0 * a3 * a4 * b8 * h ^ 50
    - (6291456 : F[X]) * a0 * a3 * b6 * h ^ 56
    + (1966080 : F[X]) * a0 * a4 ^ 3 * h ^ 53 * Polynomial.C lambda
    + (5505024 : F[X]) * a0 * a4 ^ 2 * b7 * h ^ 50
    - (5242880 : F[X]) * a0 * a4 * b5 * h ^ 56

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 240. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk24 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (6291456 : F[X]) * a0 * b3 * h ^ 62
    + (7864320 : F[X]) * a1 ^ 2 * a3 * h ^ 60
    - (2359296 : F[X]) * a1 ^ 2 * a4 * h ^ 59 * Polynomial.C lambda
    - (3670016 : F[X]) * a1 ^ 2 * b7 * h ^ 56
    + (7864320 : F[X]) * a1 * a2 ^ 2 * h ^ 60
    - (4718592 : F[X]) * a1 * a2 * a3 * h ^ 59 * Polynomial.C lambda
    - (19660800 : F[X]) * a1 * a2 * a4 ^ 2 * h ^ 54
    + (12582912 : F[X]) * a1 * a2 * a4 * b8 * h ^ 50
    - (6291456 : F[X]) * a1 * a2 * b6 * h ^ 56
    - (19660800 : F[X]) * a1 * a3 ^ 2 * a4 * h ^ 54

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 250. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk25 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (6291456 : F[X]) * a1 * a3 ^ 2 * b8 * h ^ 50
    + (5898240 : F[X]) * a1 * a3 * a4 ^ 2 * h ^ 53 * Polynomial.C lambda
    + (11010048 : F[X]) * a1 * a3 * a4 * b7 * h ^ 50
    - (5242880 : F[X]) * a1 * a3 * b5 * h ^ 56
    + (5734400 : F[X]) * a1 * a4 ^ 4 * h ^ 48
    - (5242880 : F[X]) * a1 * a4 ^ 3 * b8 * h ^ 44
    + (4718592 : F[X]) * a1 * a4 ^ 2 * b6 * h ^ 50
    - (4194304 : F[X]) * a1 * a4 * b4 * h ^ 56
    + (4194304 : F[X]) * a1 * b2 * h ^ 62
    - (786432 : F[X]) * a2 ^ 3 * h ^ 59 * Polynomial.C lambda

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 260. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk26 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    - (19660800 : F[X]) * a2 ^ 2 * a3 * a4 * h ^ 54
    + (6291456 : F[X]) * a2 ^ 2 * a3 * b8 * h ^ 50
    + (2949120 : F[X]) * a2 ^ 2 * a4 ^ 2 * h ^ 53 * Polynomial.C lambda
    + (5505024 : F[X]) * a2 ^ 2 * a4 * b7 * h ^ 50
    - (2621440 : F[X]) * a2 ^ 2 * b5 * h ^ 56
    - (6553600 : F[X]) * a2 * a3 ^ 3 * h ^ 54
    + (5898240 : F[X]) * a2 * a3 ^ 2 * a4 * h ^ 53 * Polynomial.C lambda
    + (5505024 : F[X]) * a2 * a3 ^ 2 * b7 * h ^ 50
    + (22937600 : F[X]) * a2 * a3 * a4 ^ 3 * h ^ 48
    - (15728640 : F[X]) * a2 * a3 * a4 ^ 2 * b8 * h ^ 44

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 270. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk27 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (9437184 : F[X]) * a2 * a3 * a4 * b6 * h ^ 50
    - (4194304 : F[X]) * a2 * a3 * b4 * h ^ 56
    - (1720320 : F[X]) * a2 * a4 ^ 4 * h ^ 47 * Polynomial.C lambda
    - (4587520 : F[X]) * a2 * a4 ^ 3 * b7 * h ^ 44
    + (3932160 : F[X]) * a2 * a4 ^ 2 * b5 * h ^ 50
    - (3145728 : F[X]) * a2 * a4 * b3 * h ^ 56
    + (2097152 : F[X]) * a2 * b1 * h ^ 62
    + (491520 : F[X]) * a3 ^ 4 * h ^ 53 * Polynomial.C lambda
    + (11468800 : F[X]) * a3 ^ 3 * a4 ^ 2 * h ^ 48
    - (5242880 : F[X]) * a3 ^ 3 * a4 * b8 * h ^ 44

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 280. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk28 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (1572864 : F[X]) * a3 ^ 3 * b6 * h ^ 50
    - (3440640 : F[X]) * a3 ^ 2 * a4 ^ 3 * h ^ 47 * Polynomial.C lambda
    - (6881280 : F[X]) * a3 ^ 2 * a4 ^ 2 * b7 * h ^ 44
    + (3932160 : F[X]) * a3 ^ 2 * a4 * b5 * h ^ 50
    - (1572864 : F[X]) * a3 ^ 2 * b3 * h ^ 56
    - (5160960 : F[X]) * a3 * a4 ^ 5 * h ^ 42
    + (4587520 : F[X]) * a3 * a4 ^ 4 * b8 * h ^ 38
    - (3932160 : F[X]) * a3 * a4 ^ 3 * b6 * h ^ 44
    + (3145728 : F[X]) * a3 * a4 ^ 2 * b4 * h ^ 50
    - (2097152 : F[X]) * a3 * a4 * b2 * h ^ 56

set_option maxHeartbeats 64000000 in
/-- Independent accumulator chunk ending at monomial 285. -/
private abbrev fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk29 (acc : F[X])
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    acc
    + (258048 : F[X]) * a4 ^ 6 * h ^ 41 * Polynomial.C lambda
    + (802816 : F[X]) * a4 ^ 5 * b7 * h ^ 38
    - (819200 : F[X]) * a4 ^ 4 * b5 * h ^ 44
    + (786432 : F[X]) * a4 ^ 3 * b3 * h ^ 50
    - (524288 : F[X]) * a4 ^ 2 * b1 * h ^ 56

set_option maxHeartbeats 64000000 in
/-- Polynomial numerator of `12582912 h⁶⁵ μ` on the ninth-power face. -/
def localClearedThirteenthDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk29
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk28
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk27
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk26
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk25
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk24
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk23
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk22
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk21
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk20
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk19
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk18
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk17
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk16
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk15
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk14
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk13
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk12
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk11
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk10
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk09
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk08
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk07
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk06
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk05
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk04
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk03
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk02
      (fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk01 h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda) h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 lambda
-- Fix the polynomial carrier for the aligned statement inside this Part.
local infixl:65 (priority := high) " + " => (HAdd.hAdd (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:65 (priority := high) " - " => (HSub.hSub (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:70 (priority := high) " * " => (HMul.hMul (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:70 (priority := high) " / " => (HDiv.hDiv (α := F[X]) (β := F[X]) (γ := F[X]))
local infixr:80 (priority := high) " ^ " => (HPow.hPow (α := F[X]) (β := Nat) (γ := F[X]))
local prefix:75 (priority := high) "-" => (Neg.neg (α := F[X]))

set_option maxHeartbeats 64000000 in
/-- Aligned specialization of the weight-sixty-five defect: the
`λ`-monomials drop. -/
theorem localClearedThirteenthDefect610_of_lambda_zero
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) :
    localClearedThirteenthDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4
        b3 b2 b1 0 =
    -(180880 : F[X]) * a5 ^ 13
    + (2015520 : F[X]) * a4 * a5 ^ 11 * h ^ 6
    + (268736 : F[X]) * a5 ^ 11 * b8 * h ^ 2
    - (2139280 : F[X]) * a3 * a5 ^ 10 * h ^ 12
    - (272272 : F[X]) * a5 ^ 10 * b7 * h ^ 8
    + (2288000 : F[X]) * a2 * a5 ^ 9 * h ^ 18
    - (7779200 : F[X]) * a4 ^ 2 * a5 ^ 9 * h ^ 12
    - (3111680 : F[X]) * a4 * a5 ^ 9 * b8 * h ^ 8
    + (274560 : F[X]) * a5 ^ 9 * b6 * h ^ 14
    - (2471040 : F[X]) * a1 * a5 ^ 8 * h ^ 24
    + (14414400 : F[X]) * a3 * a4 * a5 ^ 8 * h ^ 18
    + (3294720 : F[X]) * a3 * a5 ^ 8 * b8 * h ^ 14
    + (2882880 : F[X]) * a4 * a5 ^ 8 * b7 * h ^ 14
    - (274560 : F[X]) * a5 ^ 8 * b5 * h ^ 20
    + (2703360 : F[X]) * a0 * a5 ^ 7 * h ^ 30
    - (13178880 : F[X]) * a2 * a4 * a5 ^ 7 * h ^ 24
    - (3514368 : F[X]) * a2 * a5 ^ 7 * b8 * h ^ 20
    - (6589440 : F[X]) * a3 ^ 2 * a5 ^ 7 * h ^ 24
    - (3075072 : F[X]) * a3 * a5 ^ 7 * b7 * h ^ 20
    + (10982400 : F[X]) * a4 ^ 3 * a5 ^ 7 * h ^ 18
    + (13178880 : F[X]) * a4 ^ 2 * a5 ^ 7 * b8 * h ^ 14
    - (2635776 : F[X]) * a4 * a5 ^ 7 * b6 * h ^ 20
    + (270336 : F[X]) * a5 ^ 7 * b4 * h ^ 26
    + (11827200 : F[X]) * a1 * a4 * a5 ^ 6 * h ^ 30
    + (3784704 : F[X]) * a1 * a5 ^ 6 * b8 * h ^ 26
    + (11827200 : F[X]) * a2 * a3 * a5 ^ 6 * h ^ 30
    + (3311616 : F[X]) * a2 * a5 ^ 6 * b7 * h ^ 26
    - (23063040 : F[X]) * a3 * a4 ^ 2 * a5 ^ 6 * h ^ 24
    - (24600576 : F[X]) * a3 * a4 * a5 ^ 6 * b8 * h ^ 20
    + (2838528 : F[X]) * a3 * a5 ^ 6 * b6 * h ^ 26
    - (10762752 : F[X]) * a4 ^ 2 * a5 ^ 6 * b7 * h ^ 20
    + (2365440 : F[X]) * a4 * a5 ^ 6 * b5 * h ^ 26
    - (258048 : F[X]) * a5 ^ 6 * b3 * h ^ 32
    - (10321920 : F[X]) * a0 * a4 * a5 ^ 5 * h ^ 36
    - (4128768 : F[X]) * a0 * a5 ^ 5 * b8 * h ^ 32
    - (10321920 : F[X]) * a1 * a3 * a5 ^ 5 * h ^ 36
    - (3612672 : F[X]) * a1 * a5 ^ 5 * b7 * h ^ 32
    - (5160960 : F[X]) * a2 ^ 2 * a5 ^ 5 * h ^ 36
    + (14192640 : F[X]) * a2 * a4 ^ 2 * a5 ^ 5 * h ^ 30
    + (22708224 : F[X]) * a2 * a4 * a5 ^ 5 * b8 * h ^ 26
    - (3096576 : F[X]) * a2 * a5 ^ 5 * b6 * h ^ 32
    + (14192640 : F[X]) * a3 ^ 2 * a4 * a5 ^ 5 * h ^ 30
    + (11354112 : F[X]) * a3 ^ 2 * a5 ^ 5 * b8 * h ^ 26
    + (19869696 : F[X]) * a3 * a4 * a5 ^ 5 * b7 * h ^ 26
    - (2580480 : F[X]) * a3 * a5 ^ 5 * b5 * h ^ 32
    - (24600576 : F[X]) * a4 ^ 3 * a5 ^ 5 * b8 * h ^ 20
    + (8515584 : F[X]) * a4 ^ 2 * a5 ^ 5 * b6 * h ^ 26
    - (2064384 : F[X]) * a4 * a5 ^ 5 * b4 * h ^ 32
    + (229376 : F[X]) * a5 ^ 5 * b2 * h ^ 38
    + (8601600 : F[X]) * a0 * a3 * a5 ^ 4 * h ^ 42
    + (4014080 : F[X]) * a0 * a5 ^ 4 * b7 * h ^ 38
    + (8601600 : F[X]) * a1 * a2 * a5 ^ 4 * h ^ 42
    - (6451200 : F[X]) * a1 * a4 ^ 2 * a5 ^ 4 * h ^ 36
    - (20643840 : F[X]) * a1 * a4 * a5 ^ 4 * b8 * h ^ 32
    + (3440640 : F[X]) * a1 * a5 ^ 4 * b6 * h ^ 38
    - (12902400 : F[X]) * a2 * a3 * a4 * a5 ^ 4 * h ^ 36
    - (20643840 : F[X]) * a2 * a3 * a5 ^ 4 * b8 * h ^ 32
    - (18063360 : F[X]) * a2 * a4 * a5 ^ 4 * b7 * h ^ 32
    + (2867200 : F[X]) * a2 * a5 ^ 4 * b5 * h ^ 38
    - (2150400 : F[X]) * a3 ^ 3 * a5 ^ 4 * h ^ 36
    - (9031680 : F[X]) * a3 ^ 2 * a5 ^ 4 * b7 * h ^ 32
    - (11827200 : F[X]) * a3 * a4 ^ 3 * a5 ^ 4 * h ^ 30
    + (56770560 : F[X]) * a3 * a4 ^ 2 * a5 ^ 4 * b8 * h ^ 26
    - (15482880 : F[X]) * a3 * a4 * a5 ^ 4 * b6 * h ^ 32
    + (2293760 : F[X]) * a3 * a5 ^ 4 * b4 * h ^ 38
    + (16558080 : F[X]) * a4 ^ 3 * a5 ^ 4 * b7 * h ^ 26
    - (6451200 : F[X]) * a4 ^ 2 * a5 ^ 4 * b5 * h ^ 32
    + (1720320 : F[X]) * a4 * a5 ^ 4 * b3 * h ^ 38
    - (163840 : F[X]) * a5 ^ 4 * b1 * h ^ 44
    - (6553600 : F[X]) * a0 * a2 * a5 ^ 3 * h ^ 48
    + (18350080 : F[X]) * a0 * a4 * a5 ^ 3 * b8 * h ^ 38
    - (3932160 : F[X]) * a0 * a5 ^ 3 * b6 * h ^ 44
    - (3276800 : F[X]) * a1 ^ 2 * a5 ^ 3 * h ^ 48
    + (18350080 : F[X]) * a1 * a3 * a5 ^ 3 * b8 * h ^ 38
    + (16056320 : F[X]) * a1 * a4 * a5 ^ 3 * b7 * h ^ 38
    - (3276800 : F[X]) * a1 * a5 ^ 3 * b5 * h ^ 44
    + (9175040 : F[X]) * a2 ^ 2 * a5 ^ 3 * b8 * h ^ 38
    + (16056320 : F[X]) * a2 * a3 * a5 ^ 3 * b7 * h ^ 38
    + (17203200 : F[X]) * a2 * a4 ^ 3 * a5 ^ 3 * h ^ 36
    - (41287680 : F[X]) * a2 * a4 ^ 2 * a5 ^ 3 * b8 * h ^ 32
    + (13762560 : F[X]) * a2 * a4 * a5 ^ 3 * b6 * h ^ 38
    - (2621440 : F[X]) * a2 * a5 ^ 3 * b4 * h ^ 44
    + (25804800 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 ^ 3 * h ^ 36
    - (41287680 : F[X]) * a3 ^ 2 * a4 * a5 ^ 3 * b8 * h ^ 32
    + (6881280 : F[X]) * a3 ^ 2 * a5 ^ 3 * b6 * h ^ 38
    - (36126720 : F[X]) * a3 * a4 ^ 2 * a5 ^ 3 * b7 * h ^ 32
    + (11468800 : F[X]) * a3 * a4 * a5 ^ 3 * b5 * h ^ 38
    - (1966080 : F[X]) * a3 * a5 ^ 3 * b3 * h ^ 44
    - (9461760 : F[X]) * a4 ^ 5 * a5 ^ 3 * h ^ 30
    + (18923520 : F[X]) * a4 ^ 4 * a5 ^ 3 * b8 * h ^ 26
    - (10321920 : F[X]) * a4 ^ 3 * a5 ^ 3 * b6 * h ^ 32
    + (4587520 : F[X]) * a4 ^ 2 * a5 ^ 3 * b4 * h ^ 38
    - (1310720 : F[X]) * a4 * a5 ^ 3 * b2 * h ^ 44
    + (3932160 : F[X]) * a0 * a1 * a5 ^ 2 * h ^ 54
    + (9830400 : F[X]) * a0 * a3 * a4 * a5 ^ 2 * h ^ 48
    - (15728640 : F[X]) * a0 * a3 * a5 ^ 2 * b8 * h ^ 44
    - (13762560 : F[X]) * a0 * a4 * a5 ^ 2 * b7 * h ^ 44
    + (3932160 : F[X]) * a0 * a5 ^ 2 * b5 * h ^ 50
    + (9830400 : F[X]) * a1 * a2 * a4 * a5 ^ 2 * h ^ 48
    - (15728640 : F[X]) * a1 * a2 * a5 ^ 2 * b8 * h ^ 44
    + (4915200 : F[X]) * a1 * a3 ^ 2 * a5 ^ 2 * h ^ 48
    - (13762560 : F[X]) * a1 * a3 * a5 ^ 2 * b7 * h ^ 44
    - (17203200 : F[X]) * a1 * a4 ^ 3 * a5 ^ 2 * h ^ 42
    + (27525120 : F[X]) * a1 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 38
    - (11796480 : F[X]) * a1 * a4 * a5 ^ 2 * b6 * h ^ 44
    + (3145728 : F[X]) * a1 * a5 ^ 2 * b4 * h ^ 50
    + (4915200 : F[X]) * a2 ^ 2 * a3 * a5 ^ 2 * h ^ 48
    - (6881280 : F[X]) * a2 ^ 2 * a5 ^ 2 * b7 * h ^ 44
    - (51609600 : F[X]) * a2 * a3 * a4 ^ 2 * a5 ^ 2 * h ^ 42
    + (55050240 : F[X]) * a2 * a3 * a4 * a5 ^ 2 * b8 * h ^ 38
    - (11796480 : F[X]) * a2 * a3 * a5 ^ 2 * b6 * h ^ 44
    + (24084480 : F[X]) * a2 * a4 ^ 2 * a5 ^ 2 * b7 * h ^ 38
    - (9830400 : F[X]) * a2 * a4 * a5 ^ 2 * b5 * h ^ 44
    + (2359296 : F[X]) * a2 * a5 ^ 2 * b3 * h ^ 50
    - (17203200 : F[X]) * a3 ^ 3 * a4 * a5 ^ 2 * h ^ 42
    + (9175040 : F[X]) * a3 ^ 3 * a5 ^ 2 * b8 * h ^ 38
    + (24084480 : F[X]) * a3 ^ 2 * a4 * a5 ^ 2 * b7 * h ^ 38
    - (4915200 : F[X]) * a3 ^ 2 * a5 ^ 2 * b5 * h ^ 44
    + (32256000 : F[X]) * a3 * a4 ^ 4 * a5 ^ 2 * h ^ 36
    - (41287680 : F[X]) * a3 * a4 ^ 3 * a5 ^ 2 * b8 * h ^ 32
    + (20643840 : F[X]) * a3 * a4 ^ 2 * a5 ^ 2 * b6 * h ^ 38
    - (7864320 : F[X]) * a3 * a4 * a5 ^ 2 * b4 * h ^ 44
    + (1572864 : F[X]) * a3 * a5 ^ 2 * b2 * h ^ 50
    - (9031680 : F[X]) * a4 ^ 4 * a5 ^ 2 * b7 * h ^ 32
    + (5734400 : F[X]) * a4 ^ 3 * a5 ^ 2 * b5 * h ^ 38
    - (2949120 : F[X]) * a4 ^ 2 * a5 ^ 2 * b3 * h ^ 44
    + (786432 : F[X]) * a4 * a5 ^ 2 * b1 * h ^ 50
    - (15728640 : F[X]) * a0 * a2 * a4 * a5 * h ^ 54
    + (12582912 : F[X]) * a0 * a2 * a5 * b8 * h ^ 50
    - (7864320 : F[X]) * a0 * a3 ^ 2 * a5 * h ^ 54
    + (11010048 : F[X]) * a0 * a3 * a5 * b7 * h ^ 50
    + (13107200 : F[X]) * a0 * a4 ^ 3 * a5 * h ^ 48
    - (15728640 : F[X]) * a0 * a4 ^ 2 * a5 * b8 * h ^ 44
    + (9437184 : F[X]) * a0 * a4 * a5 * b6 * h ^ 50
    - (4194304 : F[X]) * a0 * a5 * b4 * h ^ 56
    - (7864320 : F[X]) * a1 ^ 2 * a4 * a5 * h ^ 54
    + (6291456 : F[X]) * a1 ^ 2 * a5 * b8 * h ^ 50
    - (15728640 : F[X]) * a1 * a2 * a3 * a5 * h ^ 54
    + (11010048 : F[X]) * a1 * a2 * a5 * b7 * h ^ 50
    + (39321600 : F[X]) * a1 * a3 * a4 ^ 2 * a5 * h ^ 48
    - (31457280 : F[X]) * a1 * a3 * a4 * a5 * b8 * h ^ 44
    + (9437184 : F[X]) * a1 * a3 * a5 * b6 * h ^ 50
    - (13762560 : F[X]) * a1 * a4 ^ 2 * a5 * b7 * h ^ 44
    + (7864320 : F[X]) * a1 * a4 * a5 * b5 * h ^ 50
    - (3145728 : F[X]) * a1 * a5 * b3 * h ^ 56
    - (2621440 : F[X]) * a2 ^ 3 * a5 * h ^ 54
    + (19660800 : F[X]) * a2 ^ 2 * a4 ^ 2 * a5 * h ^ 48
    - (15728640 : F[X]) * a2 ^ 2 * a4 * a5 * b8 * h ^ 44
    + (4718592 : F[X]) * a2 ^ 2 * a5 * b6 * h ^ 50
    + (39321600 : F[X]) * a2 * a3 ^ 2 * a4 * a5 * h ^ 48
    - (15728640 : F[X]) * a2 * a3 ^ 2 * a5 * b8 * h ^ 44
    - (27525120 : F[X]) * a2 * a3 * a4 * a5 * b7 * h ^ 44
    + (7864320 : F[X]) * a2 * a3 * a5 * b5 * h ^ 50
    - (17203200 : F[X]) * a2 * a4 ^ 4 * a5 * h ^ 42
    + (18350080 : F[X]) * a2 * a4 ^ 3 * a5 * b8 * h ^ 38
    - (11796480 : F[X]) * a2 * a4 ^ 2 * a5 * b6 * h ^ 44
    + (6291456 : F[X]) * a2 * a4 * a5 * b4 * h ^ 50
    - (2097152 : F[X]) * a2 * a5 * b2 * h ^ 56
    + (3276800 : F[X]) * a3 ^ 4 * a5 * h ^ 48
    - (4587520 : F[X]) * a3 ^ 3 * a5 * b7 * h ^ 44
    - (34406400 : F[X]) * a3 ^ 2 * a4 ^ 3 * a5 * h ^ 42
    + (27525120 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 * b8 * h ^ 38
    - (11796480 : F[X]) * a3 ^ 2 * a4 * a5 * b6 * h ^ 44
    + (3145728 : F[X]) * a3 ^ 2 * a5 * b4 * h ^ 50
    + (16056320 : F[X]) * a3 * a4 ^ 3 * a5 * b7 * h ^ 38
    - (9830400 : F[X]) * a3 * a4 ^ 2 * a5 * b5 * h ^ 44
    + (4718592 : F[X]) * a3 * a4 * a5 * b3 * h ^ 50
    - (1048576 : F[X]) * a3 * a5 * b1 * h ^ 56
    + (3440640 : F[X]) * a4 ^ 6 * a5 * h ^ 36
    - (4128768 : F[X]) * a4 ^ 5 * a5 * b8 * h ^ 32
    + (3440640 : F[X]) * a4 ^ 4 * a5 * b6 * h ^ 38
    - (2621440 : F[X]) * a4 ^ 3 * a5 * b4 * h ^ 44
    + (1572864 : F[X]) * a4 ^ 2 * a5 * b2 * h ^ 50
    + (15728640 : F[X]) * a0 * a1 * a4 * h ^ 60
    - (8388608 : F[X]) * a0 * a1 * b8 * h ^ 56
    + (15728640 : F[X]) * a0 * a2 * a3 * h ^ 60
    - (7340032 : F[X]) * a0 * a2 * b7 * h ^ 56
    - (19660800 : F[X]) * a0 * a3 * a4 ^ 2 * h ^ 54
    + (12582912 : F[X]) * a0 * a3 * a4 * b8 * h ^ 50
    - (6291456 : F[X]) * a0 * a3 * b6 * h ^ 56
    + (5505024 : F[X]) * a0 * a4 ^ 2 * b7 * h ^ 50
    - (5242880 : F[X]) * a0 * a4 * b5 * h ^ 56
    + (6291456 : F[X]) * a0 * b3 * h ^ 62
    + (7864320 : F[X]) * a1 ^ 2 * a3 * h ^ 60
    - (3670016 : F[X]) * a1 ^ 2 * b7 * h ^ 56
    + (7864320 : F[X]) * a1 * a2 ^ 2 * h ^ 60
    - (19660800 : F[X]) * a1 * a2 * a4 ^ 2 * h ^ 54
    + (12582912 : F[X]) * a1 * a2 * a4 * b8 * h ^ 50
    - (6291456 : F[X]) * a1 * a2 * b6 * h ^ 56
    - (19660800 : F[X]) * a1 * a3 ^ 2 * a4 * h ^ 54
    + (6291456 : F[X]) * a1 * a3 ^ 2 * b8 * h ^ 50
    + (11010048 : F[X]) * a1 * a3 * a4 * b7 * h ^ 50
    - (5242880 : F[X]) * a1 * a3 * b5 * h ^ 56
    + (5734400 : F[X]) * a1 * a4 ^ 4 * h ^ 48
    - (5242880 : F[X]) * a1 * a4 ^ 3 * b8 * h ^ 44
    + (4718592 : F[X]) * a1 * a4 ^ 2 * b6 * h ^ 50
    - (4194304 : F[X]) * a1 * a4 * b4 * h ^ 56
    + (4194304 : F[X]) * a1 * b2 * h ^ 62
    - (19660800 : F[X]) * a2 ^ 2 * a3 * a4 * h ^ 54
    + (6291456 : F[X]) * a2 ^ 2 * a3 * b8 * h ^ 50
    + (5505024 : F[X]) * a2 ^ 2 * a4 * b7 * h ^ 50
    - (2621440 : F[X]) * a2 ^ 2 * b5 * h ^ 56
    - (6553600 : F[X]) * a2 * a3 ^ 3 * h ^ 54
    + (5505024 : F[X]) * a2 * a3 ^ 2 * b7 * h ^ 50
    + (22937600 : F[X]) * a2 * a3 * a4 ^ 3 * h ^ 48
    - (15728640 : F[X]) * a2 * a3 * a4 ^ 2 * b8 * h ^ 44
    + (9437184 : F[X]) * a2 * a3 * a4 * b6 * h ^ 50
    - (4194304 : F[X]) * a2 * a3 * b4 * h ^ 56
    - (4587520 : F[X]) * a2 * a4 ^ 3 * b7 * h ^ 44
    + (3932160 : F[X]) * a2 * a4 ^ 2 * b5 * h ^ 50
    - (3145728 : F[X]) * a2 * a4 * b3 * h ^ 56
    + (2097152 : F[X]) * a2 * b1 * h ^ 62
    + (11468800 : F[X]) * a3 ^ 3 * a4 ^ 2 * h ^ 48
    - (5242880 : F[X]) * a3 ^ 3 * a4 * b8 * h ^ 44
    + (1572864 : F[X]) * a3 ^ 3 * b6 * h ^ 50
    - (6881280 : F[X]) * a3 ^ 2 * a4 ^ 2 * b7 * h ^ 44
    + (3932160 : F[X]) * a3 ^ 2 * a4 * b5 * h ^ 50
    - (1572864 : F[X]) * a3 ^ 2 * b3 * h ^ 56
    - (5160960 : F[X]) * a3 * a4 ^ 5 * h ^ 42
    + (4587520 : F[X]) * a3 * a4 ^ 4 * b8 * h ^ 38
    - (3932160 : F[X]) * a3 * a4 ^ 3 * b6 * h ^ 44
    + (3145728 : F[X]) * a3 * a4 ^ 2 * b4 * h ^ 50
    - (2097152 : F[X]) * a3 * a4 * b2 * h ^ 56
    + (802816 : F[X]) * a4 ^ 5 * b7 * h ^ 38
    - (819200 : F[X]) * a4 ^ 4 * b5 * h ^ 44
    + (786432 : F[X]) * a4 ^ 3 * b3 * h ^ 50
    - (524288 : F[X]) * a4 ^ 2 * b1 * h ^ 56     := by
  simp [localClearedThirteenthDefect610, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk01, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk02, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk03, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk04, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk05, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk06, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk07, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk08, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk09, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk10, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk11, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk12, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk13, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk14, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk15, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk16, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk17, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk18, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk19, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk20, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk21, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk22, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk23, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk24, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk25, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk26, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk27, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk28, fable610twelfthSpeedT_localClearedThirteenthDefect610_chunk29, map_zero]



end Depression610Thirteenth

end ScaleZeroTwelfthDefect610
end Max11DegreeRoutes
end
