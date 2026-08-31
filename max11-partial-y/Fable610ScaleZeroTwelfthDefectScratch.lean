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

set_option maxRecDepth 1000000

section ScaleZeroTwelfthDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/


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
set_option maxHeartbeats 16000000 in
/-- Polynomial numerator of `12582912 h⁶⁵ μ` on the ninth-power face. -/
def localClearedThirteenthDefect610
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
    + (258048 : F[X]) * a4 ^ 6 * h ^ 41 * Polynomial.C lambda
    + (802816 : F[X]) * a4 ^ 5 * b7 * h ^ 38
    - (819200 : F[X]) * a4 ^ 4 * b5 * h ^ 44
    + (786432 : F[X]) * a4 ^ 3 * b3 * h ^ 50
    - (524288 : F[X]) * a4 ^ 2 * b1 * h ^ 56
set_option maxHeartbeats 16000000 in
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
  simp [localClearedThirteenthDefect610, map_zero]


set_option maxHeartbeats 400000000 in
/-- Clearing the first integral `μ` of the degree-`2` row against `h⁶⁵`
on the ninth-power face. -/
theorem thirteenthDefect_eq_clearedMu610
    (h a5 a4 a3 a2 a1 a0 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda : F)
    (hh : h ≠ 0)
    (hN : 5 * a5 * h ^ 4 - 3 * b9 = lambda * h ^ 9) :
    (12582912 : F) * h ^ 65 *
        muResidual610
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
          (depressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5
            b4 b3 b2 b1) =
    -(180880 : F) * a5 ^ 13
    + (88179 : F) * a5 ^ 12 * h ^ 5 * lambda
    + (2015520 : F) * a4 * a5 ^ 11 * h ^ 6
    + (268736 : F) * a5 ^ 11 * b8 * h ^ 2
    - (2139280 : F) * a3 * a5 ^ 10 * h ^ 12
    - (1108536 : F) * a4 * a5 ^ 10 * h ^ 11 * lambda
    - (272272 : F) * a5 ^ 10 * b7 * h ^ 8
    + (2288000 : F) * a2 * a5 ^ 9 * h ^ 18
    + (1166880 : F) * a3 * a5 ^ 9 * h ^ 17 * lambda
    - (7779200 : F) * a4 ^ 2 * a5 ^ 9 * h ^ 12
    - (3111680 : F) * a4 * a5 ^ 9 * b8 * h ^ 8
    + (274560 : F) * a5 ^ 9 * b6 * h ^ 14
    - (2471040 : F) * a1 * a5 ^ 8 * h ^ 24
    - (1235520 : F) * a2 * a5 ^ 8 * h ^ 23 * lambda
    + (14414400 : F) * a3 * a4 * a5 ^ 8 * h ^ 18
    + (3294720 : F) * a3 * a5 ^ 8 * b8 * h ^ 14
    + (5250960 : F) * a4 ^ 2 * a5 ^ 8 * h ^ 17 * lambda
    + (2882880 : F) * a4 * a5 ^ 8 * b7 * h ^ 14
    - (274560 : F) * a5 ^ 8 * b5 * h ^ 20
    + (2703360 : F) * a0 * a5 ^ 7 * h ^ 30
    + (1317888 : F) * a1 * a5 ^ 7 * h ^ 29 * lambda
    - (13178880 : F) * a2 * a4 * a5 ^ 7 * h ^ 24
    - (3514368 : F) * a2 * a5 ^ 7 * b8 * h ^ 20
    - (6589440 : F) * a3 ^ 2 * a5 ^ 7 * h ^ 24
    - (9884160 : F) * a3 * a4 * a5 ^ 7 * h ^ 23 * lambda
    - (3075072 : F) * a3 * a5 ^ 7 * b7 * h ^ 20
    + (10982400 : F) * a4 ^ 3 * a5 ^ 7 * h ^ 18
    + (13178880 : F) * a4 ^ 2 * a5 ^ 7 * b8 * h ^ 14
    - (2635776 : F) * a4 * a5 ^ 7 * b6 * h ^ 20
    + (270336 : F) * a5 ^ 7 * b4 * h ^ 26
    - (1419264 : F) * a0 * a5 ^ 6 * h ^ 35 * lambda
    + (11827200 : F) * a1 * a4 * a5 ^ 6 * h ^ 30
    + (3784704 : F) * a1 * a5 ^ 6 * b8 * h ^ 26
    + (11827200 : F) * a2 * a3 * a5 ^ 6 * h ^ 30
    + (9225216 : F) * a2 * a4 * a5 ^ 6 * h ^ 29 * lambda
    + (3311616 : F) * a2 * a5 ^ 6 * b7 * h ^ 26
    + (4612608 : F) * a3 ^ 2 * a5 ^ 6 * h ^ 29 * lambda
    - (23063040 : F) * a3 * a4 ^ 2 * a5 ^ 6 * h ^ 24
    - (24600576 : F) * a3 * a4 * a5 ^ 6 * b8 * h ^ 20
    + (2838528 : F) * a3 * a5 ^ 6 * b6 * h ^ 26
    - (11531520 : F) * a4 ^ 3 * a5 ^ 6 * h ^ 23 * lambda
    - (10762752 : F) * a4 ^ 2 * a5 ^ 6 * b7 * h ^ 20
    + (2365440 : F) * a4 * a5 ^ 6 * b5 * h ^ 26
    - (258048 : F) * a5 ^ 6 * b3 * h ^ 32
    - (10321920 : F) * a0 * a4 * a5 ^ 5 * h ^ 36
    - (4128768 : F) * a0 * a5 ^ 5 * b8 * h ^ 32
    - (10321920 : F) * a1 * a3 * a5 ^ 5 * h ^ 36
    - (8515584 : F) * a1 * a4 * a5 ^ 5 * h ^ 35 * lambda
    - (3612672 : F) * a1 * a5 ^ 5 * b7 * h ^ 32
    - (5160960 : F) * a2 ^ 2 * a5 ^ 5 * h ^ 36
    - (8515584 : F) * a2 * a3 * a5 ^ 5 * h ^ 35 * lambda
    + (14192640 : F) * a2 * a4 ^ 2 * a5 ^ 5 * h ^ 30
    + (22708224 : F) * a2 * a4 * a5 ^ 5 * b8 * h ^ 26
    - (3096576 : F) * a2 * a5 ^ 5 * b6 * h ^ 32
    + (14192640 : F) * a3 ^ 2 * a4 * a5 ^ 5 * h ^ 30
    + (11354112 : F) * a3 ^ 2 * a5 ^ 5 * b8 * h ^ 26
    + (27675648 : F) * a3 * a4 ^ 2 * a5 ^ 5 * h ^ 29 * lambda
    + (19869696 : F) * a3 * a4 * a5 ^ 5 * b7 * h ^ 26
    - (2580480 : F) * a3 * a5 ^ 5 * b5 * h ^ 32
    - (24600576 : F) * a4 ^ 3 * a5 ^ 5 * b8 * h ^ 20
    + (8515584 : F) * a4 ^ 2 * a5 ^ 5 * b6 * h ^ 26
    - (2064384 : F) * a4 * a5 ^ 5 * b4 * h ^ 32
    + (229376 : F) * a5 ^ 5 * b2 * h ^ 38
    + (8601600 : F) * a0 * a3 * a5 ^ 4 * h ^ 42
    + (7741440 : F) * a0 * a4 * a5 ^ 4 * h ^ 41 * lambda
    + (4014080 : F) * a0 * a5 ^ 4 * b7 * h ^ 38
    + (8601600 : F) * a1 * a2 * a5 ^ 4 * h ^ 42
    + (7741440 : F) * a1 * a3 * a5 ^ 4 * h ^ 41 * lambda
    - (6451200 : F) * a1 * a4 ^ 2 * a5 ^ 4 * h ^ 36
    - (20643840 : F) * a1 * a4 * a5 ^ 4 * b8 * h ^ 32
    + (3440640 : F) * a1 * a5 ^ 4 * b6 * h ^ 38
    + (3870720 : F) * a2 ^ 2 * a5 ^ 4 * h ^ 41 * lambda
    - (12902400 : F) * a2 * a3 * a4 * a5 ^ 4 * h ^ 36
    - (20643840 : F) * a2 * a3 * a5 ^ 4 * b8 * h ^ 32
    - (21288960 : F) * a2 * a4 ^ 2 * a5 ^ 4 * h ^ 35 * lambda
    - (18063360 : F) * a2 * a4 * a5 ^ 4 * b7 * h ^ 32
    + (2867200 : F) * a2 * a5 ^ 4 * b5 * h ^ 38
    - (2150400 : F) * a3 ^ 3 * a5 ^ 4 * h ^ 36
    - (21288960 : F) * a3 ^ 2 * a4 * a5 ^ 4 * h ^ 35 * lambda
    - (9031680 : F) * a3 ^ 2 * a5 ^ 4 * b7 * h ^ 32
    - (11827200 : F) * a3 * a4 ^ 3 * a5 ^ 4 * h ^ 30
    + (56770560 : F) * a3 * a4 ^ 2 * a5 ^ 4 * b8 * h ^ 26
    - (15482880 : F) * a3 * a4 * a5 ^ 4 * b6 * h ^ 32
    + (2293760 : F) * a3 * a5 ^ 4 * b4 * h ^ 38
    + (11531520 : F) * a4 ^ 4 * a5 ^ 4 * h ^ 29 * lambda
    + (16558080 : F) * a4 ^ 3 * a5 ^ 4 * b7 * h ^ 26
    - (6451200 : F) * a4 ^ 2 * a5 ^ 4 * b5 * h ^ 32
    + (1720320 : F) * a4 * a5 ^ 4 * b3 * h ^ 38
    - (163840 : F) * a5 ^ 4 * b1 * h ^ 44
    - (6553600 : F) * a0 * a2 * a5 ^ 3 * h ^ 48
    - (6881280 : F) * a0 * a3 * a5 ^ 3 * h ^ 47 * lambda
    + (18350080 : F) * a0 * a4 * a5 ^ 3 * b8 * h ^ 38
    - (3932160 : F) * a0 * a5 ^ 3 * b6 * h ^ 44
    - (3276800 : F) * a1 ^ 2 * a5 ^ 3 * h ^ 48
    - (6881280 : F) * a1 * a2 * a5 ^ 3 * h ^ 47 * lambda
    + (18350080 : F) * a1 * a3 * a5 ^ 3 * b8 * h ^ 38
    + (15482880 : F) * a1 * a4 ^ 2 * a5 ^ 3 * h ^ 41 * lambda
    + (16056320 : F) * a1 * a4 * a5 ^ 3 * b7 * h ^ 38
    - (3276800 : F) * a1 * a5 ^ 3 * b5 * h ^ 44
    + (9175040 : F) * a2 ^ 2 * a5 ^ 3 * b8 * h ^ 38
    + (30965760 : F) * a2 * a3 * a4 * a5 ^ 3 * h ^ 41 * lambda
    + (16056320 : F) * a2 * a3 * a5 ^ 3 * b7 * h ^ 38
    + (17203200 : F) * a2 * a4 ^ 3 * a5 ^ 3 * h ^ 36
    - (41287680 : F) * a2 * a4 ^ 2 * a5 ^ 3 * b8 * h ^ 32
    + (13762560 : F) * a2 * a4 * a5 ^ 3 * b6 * h ^ 38
    - (2621440 : F) * a2 * a5 ^ 3 * b4 * h ^ 44
    + (5160960 : F) * a3 ^ 3 * a5 ^ 3 * h ^ 41 * lambda
    + (25804800 : F) * a3 ^ 2 * a4 ^ 2 * a5 ^ 3 * h ^ 36
    - (41287680 : F) * a3 ^ 2 * a4 * a5 ^ 3 * b8 * h ^ 32
    + (6881280 : F) * a3 ^ 2 * a5 ^ 3 * b6 * h ^ 38
    - (28385280 : F) * a3 * a4 ^ 3 * a5 ^ 3 * h ^ 35 * lambda
    - (36126720 : F) * a3 * a4 ^ 2 * a5 ^ 3 * b7 * h ^ 32
    + (11468800 : F) * a3 * a4 * a5 ^ 3 * b5 * h ^ 38
    - (1966080 : F) * a3 * a5 ^ 3 * b3 * h ^ 44
    - (9461760 : F) * a4 ^ 5 * a5 ^ 3 * h ^ 30
    + (18923520 : F) * a4 ^ 4 * a5 ^ 3 * b8 * h ^ 26
    - (10321920 : F) * a4 ^ 3 * a5 ^ 3 * b6 * h ^ 32
    + (4587520 : F) * a4 ^ 2 * a5 ^ 3 * b4 * h ^ 38
    - (1310720 : F) * a4 * a5 ^ 3 * b2 * h ^ 44
    + (3932160 : F) * a0 * a1 * a5 ^ 2 * h ^ 54
    + (5898240 : F) * a0 * a2 * a5 ^ 2 * h ^ 53 * lambda
    + (9830400 : F) * a0 * a3 * a4 * a5 ^ 2 * h ^ 48
    - (15728640 : F) * a0 * a3 * a5 ^ 2 * b8 * h ^ 44
    - (10321920 : F) * a0 * a4 ^ 2 * a5 ^ 2 * h ^ 47 * lambda
    - (13762560 : F) * a0 * a4 * a5 ^ 2 * b7 * h ^ 44
    + (3932160 : F) * a0 * a5 ^ 2 * b5 * h ^ 50
    + (2949120 : F) * a1 ^ 2 * a5 ^ 2 * h ^ 53 * lambda
    + (9830400 : F) * a1 * a2 * a4 * a5 ^ 2 * h ^ 48
    - (15728640 : F) * a1 * a2 * a5 ^ 2 * b8 * h ^ 44
    + (4915200 : F) * a1 * a3 ^ 2 * a5 ^ 2 * h ^ 48
    - (20643840 : F) * a1 * a3 * a4 * a5 ^ 2 * h ^ 47 * lambda
    - (13762560 : F) * a1 * a3 * a5 ^ 2 * b7 * h ^ 44
    - (17203200 : F) * a1 * a4 ^ 3 * a5 ^ 2 * h ^ 42
    + (27525120 : F) * a1 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 38
    - (11796480 : F) * a1 * a4 * a5 ^ 2 * b6 * h ^ 44
    + (3145728 : F) * a1 * a5 ^ 2 * b4 * h ^ 50
    + (4915200 : F) * a2 ^ 2 * a3 * a5 ^ 2 * h ^ 48
    - (10321920 : F) * a2 ^ 2 * a4 * a5 ^ 2 * h ^ 47 * lambda
    - (6881280 : F) * a2 ^ 2 * a5 ^ 2 * b7 * h ^ 44
    - (10321920 : F) * a2 * a3 ^ 2 * a5 ^ 2 * h ^ 47 * lambda
    - (51609600 : F) * a2 * a3 * a4 ^ 2 * a5 ^ 2 * h ^ 42
    + (55050240 : F) * a2 * a3 * a4 * a5 ^ 2 * b8 * h ^ 38
    - (11796480 : F) * a2 * a3 * a5 ^ 2 * b6 * h ^ 44
    + (15482880 : F) * a2 * a4 ^ 3 * a5 ^ 2 * h ^ 41 * lambda
    + (24084480 : F) * a2 * a4 ^ 2 * a5 ^ 2 * b7 * h ^ 38
    - (9830400 : F) * a2 * a4 * a5 ^ 2 * b5 * h ^ 44
    + (2359296 : F) * a2 * a5 ^ 2 * b3 * h ^ 50
    - (17203200 : F) * a3 ^ 3 * a4 * a5 ^ 2 * h ^ 42
    + (9175040 : F) * a3 ^ 3 * a5 ^ 2 * b8 * h ^ 38
    + (23224320 : F) * a3 ^ 2 * a4 ^ 2 * a5 ^ 2 * h ^ 41 * lambda
    + (24084480 : F) * a3 ^ 2 * a4 * a5 ^ 2 * b7 * h ^ 38
    - (4915200 : F) * a3 ^ 2 * a5 ^ 2 * b5 * h ^ 44
    + (32256000 : F) * a3 * a4 ^ 4 * a5 ^ 2 * h ^ 36
    - (41287680 : F) * a3 * a4 ^ 3 * a5 ^ 2 * b8 * h ^ 32
    + (20643840 : F) * a3 * a4 ^ 2 * a5 ^ 2 * b6 * h ^ 38
    - (7864320 : F) * a3 * a4 * a5 ^ 2 * b4 * h ^ 44
    + (1572864 : F) * a3 * a5 ^ 2 * b2 * h ^ 50
    - (4257792 : F) * a4 ^ 5 * a5 ^ 2 * h ^ 35 * lambda
    - (9031680 : F) * a4 ^ 4 * a5 ^ 2 * b7 * h ^ 32
    + (5734400 : F) * a4 ^ 3 * a5 ^ 2 * b5 * h ^ 38
    - (2949120 : F) * a4 ^ 2 * a5 ^ 2 * b3 * h ^ 44
    + (786432 : F) * a4 * a5 ^ 2 * b1 * h ^ 50
    - (4718592 : F) * a0 * a1 * a5 * h ^ 59 * lambda
    - (15728640 : F) * a0 * a2 * a4 * a5 * h ^ 54
    + (12582912 : F) * a0 * a2 * a5 * b8 * h ^ 50
    - (7864320 : F) * a0 * a3 ^ 2 * a5 * h ^ 54
    + (11796480 : F) * a0 * a3 * a4 * a5 * h ^ 53 * lambda
    + (11010048 : F) * a0 * a3 * a5 * b7 * h ^ 50
    + (13107200 : F) * a0 * a4 ^ 3 * a5 * h ^ 48
    - (15728640 : F) * a0 * a4 ^ 2 * a5 * b8 * h ^ 44
    + (9437184 : F) * a0 * a4 * a5 * b6 * h ^ 50
    - (4194304 : F) * a0 * a5 * b4 * h ^ 56
    - (7864320 : F) * a1 ^ 2 * a4 * a5 * h ^ 54
    + (6291456 : F) * a1 ^ 2 * a5 * b8 * h ^ 50
    - (15728640 : F) * a1 * a2 * a3 * a5 * h ^ 54
    + (11796480 : F) * a1 * a2 * a4 * a5 * h ^ 53 * lambda
    + (11010048 : F) * a1 * a2 * a5 * b7 * h ^ 50
    + (5898240 : F) * a1 * a3 ^ 2 * a5 * h ^ 53 * lambda
    + (39321600 : F) * a1 * a3 * a4 ^ 2 * a5 * h ^ 48
    - (31457280 : F) * a1 * a3 * a4 * a5 * b8 * h ^ 44
    + (9437184 : F) * a1 * a3 * a5 * b6 * h ^ 50
    - (6881280 : F) * a1 * a4 ^ 3 * a5 * h ^ 47 * lambda
    - (13762560 : F) * a1 * a4 ^ 2 * a5 * b7 * h ^ 44
    + (7864320 : F) * a1 * a4 * a5 * b5 * h ^ 50
    - (3145728 : F) * a1 * a5 * b3 * h ^ 56
    - (2621440 : F) * a2 ^ 3 * a5 * h ^ 54
    + (5898240 : F) * a2 ^ 2 * a3 * a5 * h ^ 53 * lambda
    + (19660800 : F) * a2 ^ 2 * a4 ^ 2 * a5 * h ^ 48
    - (15728640 : F) * a2 ^ 2 * a4 * a5 * b8 * h ^ 44
    + (4718592 : F) * a2 ^ 2 * a5 * b6 * h ^ 50
    + (39321600 : F) * a2 * a3 ^ 2 * a4 * a5 * h ^ 48
    - (15728640 : F) * a2 * a3 ^ 2 * a5 * b8 * h ^ 44
    - (20643840 : F) * a2 * a3 * a4 ^ 2 * a5 * h ^ 47 * lambda
    - (27525120 : F) * a2 * a3 * a4 * a5 * b7 * h ^ 44
    + (7864320 : F) * a2 * a3 * a5 * b5 * h ^ 50
    - (17203200 : F) * a2 * a4 ^ 4 * a5 * h ^ 42
    + (18350080 : F) * a2 * a4 ^ 3 * a5 * b8 * h ^ 38
    - (11796480 : F) * a2 * a4 ^ 2 * a5 * b6 * h ^ 44
    + (6291456 : F) * a2 * a4 * a5 * b4 * h ^ 50
    - (2097152 : F) * a2 * a5 * b2 * h ^ 56
    + (3276800 : F) * a3 ^ 4 * a5 * h ^ 48
    - (6881280 : F) * a3 ^ 3 * a4 * a5 * h ^ 47 * lambda
    - (4587520 : F) * a3 ^ 3 * a5 * b7 * h ^ 44
    - (34406400 : F) * a3 ^ 2 * a4 ^ 3 * a5 * h ^ 42
    + (27525120 : F) * a3 ^ 2 * a4 ^ 2 * a5 * b8 * h ^ 38
    - (11796480 : F) * a3 ^ 2 * a4 * a5 * b6 * h ^ 44
    + (3145728 : F) * a3 ^ 2 * a5 * b4 * h ^ 50
    + (7741440 : F) * a3 * a4 ^ 4 * a5 * h ^ 41 * lambda
    + (16056320 : F) * a3 * a4 ^ 3 * a5 * b7 * h ^ 38
    - (9830400 : F) * a3 * a4 ^ 2 * a5 * b5 * h ^ 44
    + (4718592 : F) * a3 * a4 * a5 * b3 * h ^ 50
    - (1048576 : F) * a3 * a5 * b1 * h ^ 56
    + (3440640 : F) * a4 ^ 6 * a5 * h ^ 36
    - (4128768 : F) * a4 ^ 5 * a5 * b8 * h ^ 32
    + (3440640 : F) * a4 ^ 4 * a5 * b6 * h ^ 38
    - (2621440 : F) * a4 ^ 3 * a5 * b4 * h ^ 44
    + (1572864 : F) * a4 ^ 2 * a5 * b2 * h ^ 50
    + (1572864 : F) * a0 ^ 2 * h ^ 65 * lambda
    + (15728640 : F) * a0 * a1 * a4 * h ^ 60
    - (8388608 : F) * a0 * a1 * b8 * h ^ 56
    + (15728640 : F) * a0 * a2 * a3 * h ^ 60
    - (4718592 : F) * a0 * a2 * a4 * h ^ 59 * lambda
    - (7340032 : F) * a0 * a2 * b7 * h ^ 56
    - (2359296 : F) * a0 * a3 ^ 2 * h ^ 59 * lambda
    - (19660800 : F) * a0 * a3 * a4 ^ 2 * h ^ 54
    + (12582912 : F) * a0 * a3 * a4 * b8 * h ^ 50
    - (6291456 : F) * a0 * a3 * b6 * h ^ 56
    + (1966080 : F) * a0 * a4 ^ 3 * h ^ 53 * lambda
    + (5505024 : F) * a0 * a4 ^ 2 * b7 * h ^ 50
    - (5242880 : F) * a0 * a4 * b5 * h ^ 56
    + (6291456 : F) * a0 * b3 * h ^ 62
    + (7864320 : F) * a1 ^ 2 * a3 * h ^ 60
    - (2359296 : F) * a1 ^ 2 * a4 * h ^ 59 * lambda
    - (3670016 : F) * a1 ^ 2 * b7 * h ^ 56
    + (7864320 : F) * a1 * a2 ^ 2 * h ^ 60
    - (4718592 : F) * a1 * a2 * a3 * h ^ 59 * lambda
    - (19660800 : F) * a1 * a2 * a4 ^ 2 * h ^ 54
    + (12582912 : F) * a1 * a2 * a4 * b8 * h ^ 50
    - (6291456 : F) * a1 * a2 * b6 * h ^ 56
    - (19660800 : F) * a1 * a3 ^ 2 * a4 * h ^ 54
    + (6291456 : F) * a1 * a3 ^ 2 * b8 * h ^ 50
    + (5898240 : F) * a1 * a3 * a4 ^ 2 * h ^ 53 * lambda
    + (11010048 : F) * a1 * a3 * a4 * b7 * h ^ 50
    - (5242880 : F) * a1 * a3 * b5 * h ^ 56
    + (5734400 : F) * a1 * a4 ^ 4 * h ^ 48
    - (5242880 : F) * a1 * a4 ^ 3 * b8 * h ^ 44
    + (4718592 : F) * a1 * a4 ^ 2 * b6 * h ^ 50
    - (4194304 : F) * a1 * a4 * b4 * h ^ 56
    + (4194304 : F) * a1 * b2 * h ^ 62
    - (786432 : F) * a2 ^ 3 * h ^ 59 * lambda
    - (19660800 : F) * a2 ^ 2 * a3 * a4 * h ^ 54
    + (6291456 : F) * a2 ^ 2 * a3 * b8 * h ^ 50
    + (2949120 : F) * a2 ^ 2 * a4 ^ 2 * h ^ 53 * lambda
    + (5505024 : F) * a2 ^ 2 * a4 * b7 * h ^ 50
    - (2621440 : F) * a2 ^ 2 * b5 * h ^ 56
    - (6553600 : F) * a2 * a3 ^ 3 * h ^ 54
    + (5898240 : F) * a2 * a3 ^ 2 * a4 * h ^ 53 * lambda
    + (5505024 : F) * a2 * a3 ^ 2 * b7 * h ^ 50
    + (22937600 : F) * a2 * a3 * a4 ^ 3 * h ^ 48
    - (15728640 : F) * a2 * a3 * a4 ^ 2 * b8 * h ^ 44
    + (9437184 : F) * a2 * a3 * a4 * b6 * h ^ 50
    - (4194304 : F) * a2 * a3 * b4 * h ^ 56
    - (1720320 : F) * a2 * a4 ^ 4 * h ^ 47 * lambda
    - (4587520 : F) * a2 * a4 ^ 3 * b7 * h ^ 44
    + (3932160 : F) * a2 * a4 ^ 2 * b5 * h ^ 50
    - (3145728 : F) * a2 * a4 * b3 * h ^ 56
    + (2097152 : F) * a2 * b1 * h ^ 62
    + (491520 : F) * a3 ^ 4 * h ^ 53 * lambda
    + (11468800 : F) * a3 ^ 3 * a4 ^ 2 * h ^ 48
    - (5242880 : F) * a3 ^ 3 * a4 * b8 * h ^ 44
    + (1572864 : F) * a3 ^ 3 * b6 * h ^ 50
    - (3440640 : F) * a3 ^ 2 * a4 ^ 3 * h ^ 47 * lambda
    - (6881280 : F) * a3 ^ 2 * a4 ^ 2 * b7 * h ^ 44
    + (3932160 : F) * a3 ^ 2 * a4 * b5 * h ^ 50
    - (1572864 : F) * a3 ^ 2 * b3 * h ^ 56
    - (5160960 : F) * a3 * a4 ^ 5 * h ^ 42
    + (4587520 : F) * a3 * a4 ^ 4 * b8 * h ^ 38
    - (3932160 : F) * a3 * a4 ^ 3 * b6 * h ^ 44
    + (3145728 : F) * a3 * a4 ^ 2 * b4 * h ^ 50
    - (2097152 : F) * a3 * a4 * b2 * h ^ 56
    + (258048 : F) * a4 ^ 6 * h ^ 41 * lambda
    + (802816 : F) * a4 ^ 5 * b7 * h ^ 38
    - (819200 : F) * a4 ^ 4 * b5 * h ^ 44
    + (786432 : F) * a4 ^ 3 * b3 * h ^ 50
    - (524288 : F) * a4 ^ 2 * b1 * h ^ 56     := by
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
  have h24 : (24 : F) ≠ 0 := by norm_num
  have h27 : (27 : F) ≠ 0 := by norm_num
  have h32 : (32 : F) ≠ 0 := by norm_num
  have h36 : (36 : F) ≠ 0 := by norm_num
  have h54 : (54 : F) ≠ 0 := by norm_num
  have h64 : (64 : F) ≠ 0 := by norm_num
  have h72 : (72 : F) ≠ 0 := by norm_num
  have h81 : (81 : F) ≠ 0 := by norm_num
  have h108 : (108 : F) ≠ 0 := by norm_num
  have h128 : (128 : F) ≠ 0 := by norm_num
  have h144 : (144 : F) ≠ 0 := by norm_num
  have h162 : (162 : F) ≠ 0 := by norm_num
  have h216 : (216 : F) ≠ 0 := by norm_num
  have h243 : (243 : F) ≠ 0 := by norm_num
  have h256 : (256 : F) ≠ 0 := by norm_num
  have h324 : (324 : F) ≠ 0 := by norm_num
  have h432 : (432 : F) ≠ 0 := by norm_num
  have h576 : (576 : F) ≠ 0 := by norm_num
  have h648 : (648 : F) ≠ 0 := by norm_num
  have h729 : (729 : F) ≠ 0 := by norm_num
  have h972 : (972 : F) ≠ 0 := by norm_num
  have h1024 : (1024 : F) ≠ 0 := by norm_num
  have h1296 : (1296 : F) ≠ 0 := by norm_num
  have h1458 : (1458 : F) ≠ 0 := by norm_num
  have h3456 : (3456 : F) ≠ 0 := by norm_num
  have h6561 : (6561 : F) ≠ 0 := by norm_num
  have h7776 : (7776 : F) ≠ 0 := by norm_num
  have h11664 : (11664 : F) ≠ 0 := by norm_num
  have h15552 : (15552 : F) ≠ 0 := by norm_num
  have h31104 : (31104 : F) ≠ 0 := by norm_num
  have h46656 : (46656 : F) ≠ 0 := by norm_num
  have h93312 : (93312 : F) ≠ 0 := by norm_num
  have h186624 : (186624 : F) ≠ 0 := by norm_num
  have h5038848 : (5038848 : F) ≠ 0 := by norm_num
  have h12582912 : (12582912 : F) ≠ 0 := by norm_num
  have hh10 : h ^ 10 ≠ 0 := pow_ne_zero 10 hh
  have hh15 : h ^ 15 ≠ 0 := pow_ne_zero 15 hh
  have hh20 : h ^ 20 ≠ 0 := pow_ne_zero 20 hh
  have hh25 : h ^ 25 ≠ 0 := pow_ne_zero 25 hh
  have hh30 : h ^ 30 ≠ 0 := pow_ne_zero 30 hh
  have hh35 : h ^ 35 ≠ 0 := pow_ne_zero 35 hh
  have hh40 : h ^ 40 ≠ 0 := pow_ne_zero 40 hh
  have hh45 : h ^ 45 ≠ 0 := pow_ne_zero 45 hh
  have hh50 : h ^ 50 ≠ 0 := pow_ne_zero 50 hh
  have hh55 : h ^ 55 ≠ 0 := pow_ne_zero 55 hh
  have hh60 : h ^ 60 ≠ 0 := pow_ne_zero 60 hh
  have hh65 : h ^ 65 ≠ 0 := pow_ne_zero 65 hh
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
  have hW :
      depressedW610 h (sexticDepressionR610 h a5) b9 b8 b7 b6 b5 b4
          b3 b2 b1 =
        (40 * a5 ^ 9 - 9 * lambda * a5 ^ 8 * h ^ 5 -
            144 * a5 ^ 7 * b8 * h ^ 2 + 756 * a5 ^ 6 * b7 * h ^ 8 -
            3888 * a5 ^ 5 * b6 * h ^ 14 + 19440 * a5 ^ 4 * b5 * h ^ 20 -
            93312 * a5 ^ 3 * b4 * h ^ 26 + 419904 * a5 ^ 2 * b3 * h ^ 32 -
            1679616 * a5 * b2 * h ^ 38 + 5038848 * b1 * h ^ 44) /
          (5038848 * h ^ 45) :=
    depressedW610_eq_cleared h a5 b9 b8 b7 b6 b5 b4 b3 b2 b1 lambda hh hN
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
  simp only [muResidual610, hL, hA, hB, hC, hD0, hE0, hP, hQ, hR, hS,
    hT, hU, hV, hW, alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610, thetaResidual610]
  field_simp [hh, h2, h3, h4, h5, h6, h8, h9, h12, h16, h18, h24, h27,
    h32, h36, h54, h64, h72, h81, h108, h128, h144, h162, h216, h243,
    h256, h324, h432, h576, h648, h729, h972, h1024, h1296, h1458,
    h3456, h6561, h7776, h11664, h15552, h31104, h46656, h93312,
    h186624, h5038848, h12582912, hh10, hh15, hh20, hh25, hh30, hh35,
    hh40, hh45, hh50, hh55, hh60, hh65]
  ring

end Depression610Thirteenth


/-! ## Degree-`2` depressed Jacobian coefficient -/

section DepressedRow610Thirteenth

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero F]


/-- For a depressed monic sextic and a monic decic, the degree-`2`
Jacobian coefficient is exactly `3 U E' + 2 V D' + W C'
- D V' - 2 C W' - 3 B X'`. -/
theorem differentialJacobian_coeff_2_monicSexticDecic
    (d : Derivation k F F) (f g : F[X])
    (_hf_high : ∀ n, 6 < n → f.coeff n = 0) (_hf6 : f.coeff 6 = 1)
    (_hf5 : f.coeff 5 = 0)
    (_hg_high : ∀ n, 10 < n → g.coeff n = 0) (_hg10 : g.coeff 10 = 1)
    (_hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 2 =
      (3 : F) * g.coeff 3 * d (f.coeff 0) +
        (2 : F) * g.coeff 2 * d (f.coeff 1) +
        (1 : F) * g.coeff 1 * d (f.coeff 2) -
          (1 : F) * f.coeff 1 * d (g.coeff 2) -
          (2 : F) * f.coeff 2 * d (g.coeff 1) -
          (3 : F) * f.coeff 3 * d (g.coeff 0) := by
  have hanti : (Finset.HasAntidiagonal.antidiagonal 2 :
      Finset (ℕ × ℕ)) =
      ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)) := by decide
  have hne02_11 : ((0, 2) : ℕ × ℕ) ≠ (1, 1) := by decide
  have hne02_20 : ((0, 2) : ℕ × ℕ) ≠ (2, 0) := by decide
  have hne11_20 : ((1, 1) : ℕ × ℕ) ≠ (2, 0) := by decide
  have hfirst :
      (coefficientDeriv d f * g.derivative).coeff 2 =
        (3 : F) * g.coeff 3 * d (f.coeff 0) +
          (2 : F) * g.coeff 2 * d (f.coeff 1) +
          (1 : F) * g.coeff 1 * d (f.coeff 2) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)),
            (coefficientDeriv d f).coeff p.1 * g.derivative.coeff p.2) =
          (coefficientDeriv d f).coeff 0 * g.derivative.coeff 2 +
            (coefficientDeriv d f).coeff 1 * g.derivative.coeff 1 +
            (coefficientDeriv d f).coeff 2 * g.derivative.coeff 0 := by
      rw [Finset.sum_insert (by simp [hne02_11, hne02_20]),
        Finset.sum_insert (by simp [hne11_20]), Finset.sum_singleton]
      ring
    have hder2g : g.derivative.coeff 2 = (3 : F) * g.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1g : g.derivative.coeff 1 = (2 : F) * g.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder0g : g.derivative.coeff 0 = (1 : F) * g.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder2g, hder1g, hder0g]
    ring
  have hsecond :
      (f.derivative * coefficientDeriv d g).coeff 2 =
        (1 : F) * f.coeff 1 * d (g.coeff 2) +
          (2 : F) * f.coeff 2 * d (g.coeff 1) +
          (3 : F) * f.coeff 3 * d (g.coeff 0) := by
    rw [Polynomial.coeff_mul, hanti]
    have hpair :
        (∑ p ∈ ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)),
            f.derivative.coeff p.1 * (coefficientDeriv d g).coeff p.2) =
          f.derivative.coeff 0 * (coefficientDeriv d g).coeff 2 +
            f.derivative.coeff 1 * (coefficientDeriv d g).coeff 1 +
            f.derivative.coeff 2 * (coefficientDeriv d g).coeff 0 := by
      rw [Finset.sum_insert (by simp [hne02_11, hne02_20]),
        Finset.sum_insert (by simp [hne11_20]), Finset.sum_singleton]
      ring
    have hder0 : f.derivative.coeff 0 = (1 : F) * f.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder1 : f.derivative.coeff 1 = (2 : F) * f.coeff 2 := by
      rw [Polynomial.coeff_derivative]; ring
    have hder2 : f.derivative.coeff 2 = (3 : F) * f.coeff 3 := by
      rw [Polynomial.coeff_derivative]; ring
    rw [hpair, coeff_coefficientDeriv, coeff_coefficientDeriv,
      coeff_coefficientDeriv, hder0, hder1, hder2]
  simp only [differentialJacobian, Polynomial.coeff_sub, hfirst, hsecond]
  ring


set_option maxHeartbeats 400000000 in
theorem muResidual610_deriv_zero
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual610 A P) = 0)
    (hbeta : d (betaResidual610 L A B Q) = 0)
    (hgamma : d (gammaResidual610 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual610 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual610 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual610 L A B C0 D0 E0 P Q R S0 U0) = 0)
    (heta : d (etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0) = 0)
    (htheta : d (thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0) = 0)
    (hrow6 : (7 : F) * Q * d E0 + (6 : F) * R * d D0 +
        (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A - (1 : F) * D0 * d R -
        (2 : F) * C0 * d S0 - (3 : F) * B * d T0 -
        (4 : F) * A * d U0 - (6 : F) * d W0 = 0)
    (hrow5 : (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A - (1 : F) * D0 * d S0 -
        (2 : F) * C0 * d T0 - (3 : F) * B * d U0 -
        (4 : F) * A * d V0 - (6 : F) * d X0 = 0)
    (hrow4 : (5 : F) * S0 * d E0 + (4 : F) * T0 * d D0 +
        (3 : F) * U0 * d C0 + (2 : F) * V0 * d B +
        (1 : F) * W0 * d A - (1 : F) * D0 * d T0 -
        (2 : F) * C0 * d U0 - (3 : F) * B * d V0 -
        (4 : F) * A * d W0 = 0)
    (hrow : (3 : F) * U0 * d E0 + (2 : F) * V0 * d D0 +
        (1 : F) * W0 * d C0 - (1 : F) * D0 * d V0 -
        (2 : F) * C0 * d W0 - (3 : F) * B * d X0 = 0) :
    d (muResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0) = 0 := by
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
  have h10n : d (10 : F) = 0 := d.map_natCast 10
  have h11n : d (11 : F) = 0 := d.map_natCast 11
  have h14n : d (14 : F) = 0 := d.map_natCast 14
  have h20n : d (20 : F) = 0 := d.map_natCast 20
  have h24n : d (24 : F) = 0 := d.map_natCast 24
  have h25n : d (25 : F) = 0 := d.map_natCast 25
  have h32n : d (32 : F) = 0 := d.map_natCast 32
  have h35n : d (35 : F) = 0 := d.map_natCast 35
  have h54n : d (54 : F) = 0 := d.map_natCast 54
  have h64n : d (64 : F) = 0 := d.map_natCast 64
  have h77n : d (77 : F) = 0 := d.map_natCast 77
  have h108n : d (108 : F) = 0 := d.map_natCast 108
  have h110n : d (110 : F) = 0 := d.map_natCast 110
  have h144n : d (144 : F) = 0 := d.map_natCast 144
  have h162n : d (162 : F) = 0 := d.map_natCast 162
  have h256n : d (256 : F) = 0 := d.map_natCast 256
  have h385n : d (385 : F) = 0 := d.map_natCast 385
  have h432n : d (432 : F) = 0 := d.map_natCast 432
  have h576n : d (576 : F) = 0 := d.map_natCast 576
  have h729n : d (729 : F) = 0 := d.map_natCast 729
  have h972n : d (972 : F) = 0 := d.map_natCast 972
  have h1024n : d (1024 : F) = 0 := d.map_natCast 1024
  have h1458n : d (1458 : F) = 0 := d.map_natCast 1458
  have h3456n : d (3456 : F) = 0 := d.map_natCast 3456
  have h15552n : d (15552 : F) = 0 := d.map_natCast 15552
  have h31104n : d (31104 : F) = 0 := d.map_natCast 31104
  have h16f : d (1 / 6 : F) = 0 := by
    simp [Derivation.leibniz_inv, h6]
  have h13 : d (1 / 3 : F) = 0 := by
    simp [Derivation.leibniz_inv, h3]
  have h18f : d (1 / 8 : F) = 0 := by
    simp [Derivation.leibniz_inv, h8]
  have h29 : d (2 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h2]
  have h536 : d (5 / 36 : F) = 0 := by
    simp [Derivation.leibniz_div, h36, h5]
  have h827 : d (8 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h8]
  have h481 : d (4 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h4]
  have h38531104 : d (385 / 31104 : F) = 0 := by
    simp [Derivation.leibniz_div, h31104n, h385n]
  have h35432 : d (35 / 432 : F) = 0 := by
    simp [Derivation.leibniz_div, h432n, h35n]
  have h3256 : d (3 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256n, h3]
  have h332 : d (3 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32n, h3]
  have h964 : d (9 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64n, h9]
  have h35729 : d (35 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729n, h35n]
  have h2081 : d (20 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h20n]
  have hsqD : d (D0 * D0) = (2 : F) * D0 * d D0 := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hquint : d (A ^ 5) = (5 : F) * A ^ 4 * d A := by
    have : A ^ 5 = A ^ 4 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquar]
    ring
  have h15n : d (15 : F) = 0 := d.map_natCast 15
  have h70n : d (70 : F) = 0 := d.map_natCast 70
  have h216n : d (216 : F) = 0 := d.map_natCast 216
  have h6561n : d (6561 : F) = 0 := d.map_natCast 6561
  have h7776n : d (7776 : F) = 0 := d.map_natCast 7776
  have hx14 : d (1 / 4 : F) = 0 := by
    simp [Derivation.leibniz_inv, h4]
  have hx19 : d (1 / 9 : F) = 0 := by
    simp [Derivation.leibniz_inv, h9]
  have hx59 : d (5 / 9 : F) = 0 := by
    simp [Derivation.leibniz_div, h9, h5]
  have hx5243 : d (5 / 243 : F) = 0 := by
    simp [Derivation.leibniz_div, h243, h5]
  have hx8729 : d (8 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729n, h8]
  have hx932 : d (9 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32n, h9]
  have hx1081 : d (10 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h10n]
  have hx15256 : d (15 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256n, h15n]
  have hx35216 : d (35 / 216 : F) = 0 := by
    simp [Derivation.leibniz_div, h216n, h35n]
  have hx356561 : d (35 / 6561 : F) = 0 := by
    simp [Derivation.leibniz_div, h6561n, h35n]
  have hx70729 : d (70 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729n, h70n]
  have hx3857776 : d (385 / 7776 : F) = 0 := by
    simp [Derivation.leibniz_div, h7776n, h385n]
  have hsqE : d (E0 * E0) = (2 : F) * E0 * d E0 := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hcubC : d (C0 ^ 3) = (3 : F) * C0 ^ 2 * d C0 := by
    have h2C : d (C0 ^ 2) = (2 : F) * C0 * d C0 := by
      simpa [pow_two] using hsqC
    simp [pow_three, Derivation.leibniz, h2C]
    ring
  have hquarB : d (B ^ 4) = (4 : F) * B ^ 3 * d B := by
    have : B ^ 4 = B ^ 3 * B := by ring
    rw [this]
    simp [Derivation.leibniz, hcubB]
    ring
  have hsext : d (A ^ 6) = (6 : F) * A ^ 5 * d A := by
    have : A ^ 6 = A ^ 5 * A := by ring
    rw [this]
    simp [Derivation.leibniz, hquint]
    ring
  have h124 : d (1 / 24 : F) = 0 := by
    simp [Derivation.leibniz_inv, h24n]
  have hm124 : d (-(1 / 24 : F)) = 0 := by
    rw [map_neg, h124, neg_zero]
  have h116 : d (1 / 16 : F) = 0 := by
    simp [Derivation.leibniz_inv, h16]
  have h227 : d (2 / 27 : F) = 0 := by
    simp [Derivation.leibniz_div, h27, h2]
  have h353456 : d (35 / 3456 : F) = 0 := by
    simp [Derivation.leibniz_div, h3456n, h35n]
  have h25432 : d (25 / 432 : F) = 0 := by
    simp [Derivation.leibniz_div, h432n, h25n]
  have h10243 : d (10 / 243 : F) = 0 := by
    simp [Derivation.leibniz_div, h243, h10n]
  have h14243 : d (14 / 243 : F) = 0 := by
    simp [Derivation.leibniz_div, h243, h14n]
  have h1681 : d (16 / 81 : F) = 0 := by
    simp [Derivation.leibniz_div, h81, h16]
  have h7715552 : d (77 / 15552 : F) = 0 := by
    simp [Derivation.leibniz_div, h15552n, h77n]
  have h35972 : d (35 / 972 : F) = 0 := by
    simp [Derivation.leibniz_div, h972n, h35n]
  have h35576 : d (35 / 576 : F) = 0 := by
    simp [Derivation.leibniz_div, h576n, h35n]
  have h7144 : d (7 / 144 : F) = 0 := by
    simp [Derivation.leibniz_div, h144n, h7]
  have h754 : d (7 / 54 : F) = 0 := by
    simp [Derivation.leibniz_div, h54n, h7]
  have h7108 : d (7 / 108 : F) = 0 := by
    simp [Derivation.leibniz_div, h108n, h7]
  have h51024 : d (5 / 1024 : F) = 0 := by
    simp [Derivation.leibniz_div, h1024n, h5]
  have h11256 : d (11 / 256 : F) = 0 := by
    simp [Derivation.leibniz_div, h256n, h11n]
  have h732 : d (7 / 32 : F) = 0 := by
    simp [Derivation.leibniz_div, h32n, h7]
  have h764 : d (7 / 64 : F) = 0 := by
    simp [Derivation.leibniz_div, h64n, h7]
  have h351458 : d (35 / 1458 : F) = 0 := by
    simp [Derivation.leibniz_div, h1458n, h35n]
  have h25729 : d (25 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729n, h25n]
  have h110729 : d (110 / 729 : F) = 0 := by
    simp [Derivation.leibniz_div, h729n, h110n]
  have h35162 : d (35 / 162 : F) = 0 := by
    simp [Derivation.leibniz_div, h162n, h35n]
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

  have hWderiv :
      d W0 = (7 / 6 : F) * Q * d E0 + R * d D0 +
        (5 / 6 : F) * S0 * d C0 + (2 / 3 : F) * T0 * d B +
        (1 / 2 : F) * U0 * d A -
        (1 / 6 : F) * D0 * d R - (1 / 3 : F) * C0 * d S0 -
        (1 / 2 : F) * B * d T0 - (2 / 3 : F) * A * d U0 := by
    linear_combination (-1 / 6 : F) * hrow6
  have hXderiv :
      d X0 = R * d E0 + (5 / 6 : F) * S0 * d D0 +
        (2 / 3 : F) * T0 * d C0 + (1 / 2 : F) * U0 * d B +
        (1 / 3 : F) * V0 * d A -
        (1 / 6 : F) * D0 * d S0 - (1 / 3 : F) * C0 * d T0 -
        (1 / 2 : F) * B * d U0 - (2 / 3 : F) * A * d V0 := by
    linear_combination (-1 / 6 : F) * hrow5
  have hrow_red := hrow
  simp only [hXderiv, hWderiv, hPderiv, hQderiv, hRderiv, hSderiv,
    hTderiv, hUderiv, hVderiv] at hrow_red
  have hrow4_red := hrow4
  simp only [hWderiv, hPderiv, hQderiv, hRderiv, hSderiv, hTderiv,
    hUderiv, hVderiv] at hrow4_red
  simp only [muResidual610, map_sub, map_add, Derivation.leibniz,
    smul_eq_mul, h124, hm124, h16f, h13, h12, h18f, hx14, hx19, h23, h29, h34,
    h38, h316, h3128, h332, h116, h732, h764, h49, h427, h481, hx59, h527,
    h536, h572, h581, hx5243, h736, h754, h772, h7108, h7144, h827,
    hx8729, hx932, h1027, hx1081, h227, h1681, hx15256, h2081, h10243,
    h14243, h20243, h25432, h25729, hx35216, h35162, h35432, h35576,
    h35729, h35972, h351296, h351458, h353456, hx356561, h51024,
    h11256, h110729, hx70729, h7715552, hx3857776, hL, halpha, hbeta,
    hgamma, hdelta, hepsilon, hzeta, heta, htheta, hsq, hsqB, hsqC,
    hsqD, hsqE, hcub, hcubB, hcubC, hquar, hquarB, hquint, hsext,
    pow_two, pow_three, zero_mul, add_zero, mul_zero]
  simp only [alphaResidual610, betaResidual610, gammaResidual610,
    deltaResidual610, epsilonResidual610, zetaResidual610,
    etaResidual610, thetaResidual610, pow_two, pow_three]
  linear_combination (1 / 6 : F) * hrow_red - (1 / 12 : F) * A * hrow4_red

end DepressedRow610Thirteenth



section NonzeroThirteenthDefect610

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 400000000 in
/-- The twelfth sextic/decic integral on a square-core ninth-power
source: the cleared defect is a scalar times `h⁶⁵`.  The weight-fifty-
five and weight-sixty residuals remain available from the tenth and
eleventh packets. -/
theorem nonzeroFace610_thirteenthDefectPowerRelation
    (p q : k[X][X]) (H h0 : k[X]) (j lambda : k)
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j)) :
    ∃ xi : k,
      localClearedThirteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C xi * h0 ^ 65 := by
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
  have hrow4 :
      (5 : RatFunc k) * g.coeff 5 * ratFuncDerivation68 (f.coeff 0) +
        (4 : RatFunc k) * g.coeff 4 * ratFuncDerivation68 (f.coeff 1) +
        (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 2) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 3) +
        (1 : RatFunc k) * g.coeff 1 * ratFuncDerivation68 (f.coeff 4) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 4) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 3) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 2) -
          (4 : RatFunc k) * f.coeff 4 * ratFuncDerivation68 (g.coeff 1) = 0 := by
    have hrow :=
      differentialJacobian_coeff_4_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 4) hbracket
    simpa [f, g, Polynomial.coeff_C, show (4 : ℕ) ≠ 0 by norm_num] using
      hrow.symm.trans hbr
  have hrow2 :
      (3 : RatFunc k) * g.coeff 3 * ratFuncDerivation68 (f.coeff 0) +
        (2 : RatFunc k) * g.coeff 2 * ratFuncDerivation68 (f.coeff 1) +
        (1 : RatFunc k) * g.coeff 1 * ratFuncDerivation68 (f.coeff 2) -
          (1 : RatFunc k) * f.coeff 1 * ratFuncDerivation68 (g.coeff 2) -
          (2 : RatFunc k) * f.coeff 2 * ratFuncDerivation68 (g.coeff 1) -
          (3 : RatFunc k) * f.coeff 3 * ratFuncDerivation68 (g.coeff 0) = 0 := by
    have hrow :=
      differentialJacobian_coeff_2_monicSexticDecic
        ratFuncDerivation68 f g hf_high hf6 hf5 hg_high hg10 hLconst
    have hbr := congrArg (fun t : (RatFunc k)[X] => t.coeff 2) hbracket
    simpa [f, g, Polynomial.coeff_C, show (2 : ℕ) ≠ 0 by norm_num] using
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
  have htheta0deriv :
      ratFuncDerivation68
        (thetaResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 1)) = 0 :=
    thetaResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 1) hLconst halpha0 hbeta0 hgamma0 hdelta0
      heps0deriv hzeta0deriv (by simpa using hrow6)
  have hmu0deriv :
      ratFuncDerivation68
        (muResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
          (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
          (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
          (g.coeff 2) (g.coeff 1)) = 0 :=
    muResidual610_deriv_zero ratFuncDerivation68 (g.coeff 9)
      (f.coeff 4) (f.coeff 3) (f.coeff 2) (f.coeff 1) (f.coeff 0)
      (g.coeff 8) (g.coeff 7) (g.coeff 6) (g.coeff 5) (g.coeff 4)
      (g.coeff 3) (g.coeff 2) (g.coeff 1) (g.coeff 0) hLconst halpha0
      hbeta0 hgamma0 hdelta0 heps0deriv hzeta0deriv heta0deriv
      htheta0deriv (by simpa using hrow6) (by simpa using hrow5)
      (by simpa using hrow4) (by simpa using hrow2)
  obtain ⟨xi0, hxi0⟩ :
      ∃ a : k,
        muResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) =
          algebraMap k (RatFunc k) a := by
    apply GCD369RatFuncConstantsOfPolynomialDerivative
      ratFuncDerivation46_polynomial
    simpa [ratFuncDerivation68, ratFuncDerivation46_apply] using
      hmu0deriv
  have hclear :
      algebraMap k[X] (RatFunc k)
          (localClearedThirteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            lambda) =
        (12582912 : RatFunc k) * hRF ^ 65 *
          muResidual610 (g.coeff 9) (f.coeff 4) (f.coeff 3)
            (f.coeff 2) (f.coeff 1) (f.coeff 0) (g.coeff 8) (g.coeff 7)
            (g.coeff 6) (g.coeff 5) (g.coeff 4) (g.coeff 3)
            (g.coeff 2) (g.coeff 1) := by
    have hF := thirteenthDefect_eq_clearedMu610 hRF a5 a4 a3 a2 a1 a0 b9
      b8 b7 b6 b5 b4 b3 b2 b1 (RatFunc.C lambda) hh
      (by simpa using hNrat)
    have hg9L : g.coeff 9 =
        depressedL610 hRF (sexticDepressionR610 hRF a5) b9 := by
      dsimp only [g]
      rw [hg9]
      simp [depressedL610, depressedL810, sexticDepressionR610,
        sourceToRatFunc68, sourceToRatFunc46, b9]
    simpa [localClearedThirteenthDefect610, map_sub, map_add, map_mul,
      map_pow, map_ofNat, map_neg, RatFunc.algebraMap_C, hRF, a5, a4, a3,
      a2, a1, a0, b8, b7, b6, b5, b4, b3, b2, b1, muResidual610,
      alphaResidual610, betaResidual610, gammaResidual610,
      deltaResidual610, epsilonResidual610, zetaResidual610,
      etaResidual610, thetaResidual610, hf4, hf3, hf2, hf1, hf0, hg1,
      hg2, hg3, hg4, hg5, hg6, hg7, hg8', hg9L] using hF.symm
  have htarget :
      algebraMap k[X] (RatFunc k)
          (localClearedThirteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
            (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
            (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
            lambda) =
        algebraMap k[X] (RatFunc k)
          (Polynomial.C (12582912 * xi0) * h0 ^ 65) := by
    rw [hclear, hxi0]
    simp [hRF, map_mul, map_pow, RatFunc.algebraMap_C, map_ofNat, map_add]
    ring
  refine ⟨12582912 * xi0, ?_⟩
  exact IsFractionRing.injective k[X] (RatFunc k) htarget
end NonzeroThirteenthDefect610

variable [IsAlgClosed k]

/-- Strongest exact twelfth residual after the constant-scale source
bridge: the cleared weight-sixty-five sextic/decic defect is a scalar
times `h⁶⁵`.  The weight-fifty-five kappa residual and the weight-sixty
lambda residual are preserved.  Both the vanishing and the nonzero
values of `λ` are permitted. -/
theorem scaleZero_twelfthClearedDefect_exists_C_610
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda alpha gamma delta eps zeta eta theta iota kappa mu nu
        xi : k),
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
        Polynomial.C kappa * (Polynomial.C t) ^ 50 ∧
      localClearedEleventhDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C mu * (Polynomial.C t) ^ 55 ∧
      localClearedTwelfthDefect610 (Polynomial.C t) (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C nu * (Polynomial.C t) ^ 60 ∧
      localClearedThirteenthDefect610 (Polynomial.C t) (p.coeff 5)
          (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C xi * (Polynomial.C t) ^ 65 := by
  obtain ⟨lambda, alpha, gamma, delta, eps, zeta, eta, theta, iota, kappa,
      mu, nu, hN, halpha, hgamma, hdelta, heps, hzeta, heta, htheta,
      hiota, hkappa, hmu, hnu⟩ :=
    scaleZero_eleventhClearedDefect_exists_C_610 hp hq hD ht hH hp6 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨xi, hxi⟩ :=
    nonzeroFace610_thirteenthDefectPowerRelation p q H (Polynomial.C t) j
      lambda hp hq hh0 hH hp6 hq10 hN hD
  exact ⟨lambda, alpha, gamma, delta, eps, zeta, eta, theta, iota, kappa,
    mu, nu, xi, hN, halpha, hgamma, hdelta, heps, hzeta, heta, htheta,
    hiota, hkappa, hmu, hnu, hxi⟩


/-- Source-facing twelfth residual packet for a normalized scale-zero
`(6,10)` pair.  The constants `λ`, `ν`, and `ξ` may vanish, and the
weight-sixty lambda first integral remains a ground constant times
`h⁶⁰`. -/
theorem normalized610ScaleZero_exists_twelfthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda nu xi : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5) *
            H ^ 2 -
        (3 : k[X]) *
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9) =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTwelfthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C nu * (Polynomial.C t) ^ 60 ∧
      localClearedThirteenthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C xi * (Polynomial.C t) ^ 65 := by
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
  obtain ⟨lambda, _a, _g, _d, _e, _z, _et, _th, _iot, _ka, _mu, nu, xi,
      hN, _hM, _hT, _hU, _hV, _hW, _hX, _hY, _hI, _hZ, _hJ, hnu, hxi⟩ :=
    scaleZero_twelfthClearedDefect_exists_C_610 hp hq hD ht hHsq
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)
  exact ⟨t, lambda, nu, xi, ht, hHsq,
    by simpa only [p, q] using hN,
    by simpa only [p, q] using hnu,
    by simpa only [p, q] using hxi⟩


/-- At scale zero the weight-sixty-five defect is a literal ground-field
constant. -/
theorem normalized610ScaleZero_twelfthClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda xi : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedThirteenthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C xi := by
  obtain ⟨t, lambda, _nu, xi, ht, hHsq, _hN, _hY, hZ⟩ :=
    normalized610ScaleZero_exists_twelfthClearedDefect hsource
  refine ⟨t, lambda, xi * t ^ 65, ht, hHsq, ?_⟩
  have hconst :
      localClearedThirteenthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C (xi * t ^ 65) := by
    rw [hZ, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) xi (t ^ 65)).symm
  exact hconst


/-- Newton degree of the twelfth cleared sextic/decic defect at scale
zero. -/
theorem normalized610ScaleZero_twelfthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedThirteenthDefect610 (Polynomial.C t)
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
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, xi, ht, hHsq, hZ⟩ :=
    normalized610ScaleZero_twelfthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hZ]
  exact (natDegree_C xi).le


/-- The eleventh packet's exact residual selector `172186884 p₀ q₄ h⁵⁶`
remains available on the twelfth packet. -/
theorem normalized610ScaleZero_eleventhSourceResidual_preserved
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda nu : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (172186884 : k[X]) * p.coeff 0 * q.coeff 4 * h0 ^ 56 =
        Polynomial.C nu -
          (localClearedTwelfthDefect610 h0 (p.coeff 5) (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
              (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
              lambda -
            (172186884 : k[X]) * p.coeff 0 * q.coeff 4 * h0 ^ 56) :=
  normalized610ScaleZero_eleventhSourceResidual hsource


/-- Exact twelfth residual selector: `6291456 p₀ q₃ h⁶²` differs from a
polynomial in the remaining thirteenth-defect monomials by a ground
constant. -/
theorem normalized610ScaleZero_twelfthSourceResidual
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda xi : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let h0 := Polynomial.C t
      (6291456 : k[X]) * p.coeff 0 * q.coeff 3 * h0 ^ 62 =
        Polynomial.C xi -
          (localClearedThirteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
              (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0)
              (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
              (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)
              lambda -
            (6291456 : k[X]) * p.coeff 0 * q.coeff 3 * h0 ^ 62) := by
  dsimp only
  obtain ⟨t, lambda, xi, ht, hHsq, hZ⟩ :=
    normalized610ScaleZero_twelfthClearedDefect_exists_C hsource
  refine ⟨t, lambda, xi, ht, hHsq, ?_⟩
  have hX := hZ
  simp only [localClearedThirteenthDefect610] at hX ⊢
  linear_combination hX


/-- Aligned/nonzero split of the scale-zero twelfth cleared defect: it
vanishes, or it is a nonzero ground-field constant. -/
theorem normalized610ScaleZero_twelfthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let W :=
        localClearedThirteenthDefect610 (Polynomial.C t)
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
          lambda
      W = 0 ∨ ∃ xi : k, xi ≠ 0 ∧ W = Polynomial.C xi := by
  dsimp only
  obtain ⟨t, lambda, xi, ht, hHsq, hZ⟩ :=
    normalized610ScaleZero_twelfthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  by_cases hxi : xi = 0
  · left
    simpa only [hxi, Polynomial.C_0] using hZ
  · exact Or.inr ⟨xi, hxi, hZ⟩

/-- Explicit zero/nonzero constant branches of both the discriminator
and the weight-sixty-five defect.  The weight-sixty lambda defect
remains a ground constant. -/
theorem normalized610ScaleZero_twelfthClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    ∃ (t lambda nu xi : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 5 * H ^ 2 - (3 : k[X]) * q.coeff 9
      let I :=
        localClearedTwelfthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
      let W :=
        localClearedThirteenthDefect610 (Polynomial.C t)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      I = Polynomial.C nu ∧
      W = Polynomial.C xi ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (nu = 0 ∧ I = 0 ∨
        nu ≠ 0 ∧ I = Polynomial.C nu) ∧
      (xi = 0 ∧ W = 0 ∨
        xi ≠ 0 ∧ W = Polynomial.C xi) := by
  dsimp only
  obtain ⟨t, lambda, nu0, xi0, ht, hHsq, hN, hYpow, hZpow⟩ :=
    normalized610ScaleZero_exists_twelfthClearedDefect hsource
  let nu : k := nu0 * t ^ 60
  let xi : k := xi0 * t ^ 65
  have hY :
      localClearedTwelfthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C nu := by
    rw [hYpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) nu0 (t ^ 60)).symm
  have hZ :
      localClearedThirteenthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C xi := by
    rw [hZpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) xi0 (t ^ 65)).symm
  refine ⟨t, lambda, nu, xi, ht, hHsq, hN, hY, hZ, ?_, ?_, ?_⟩
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
  · by_cases hnu : nu = 0
    · left
      refine ⟨hnu, ?_⟩
      simpa only [hnu, Polynomial.C_0] using hY
    · exact Or.inr ⟨hnu, hY⟩
  · by_cases hxi : xi = 0
    · left
      refine ⟨hxi, ?_⟩
      simpa only [hxi, Polynomial.C_0] using hZ
    · exact Or.inr ⟨hxi, hZ⟩


/-- Aligned branch `N = 0`: the weight-sixty-five defect is still a
ground constant, now with `λ = 0`. -/
theorem normalized610ScaleZero_twelfthClearedDefect_of_aligned
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (haligned :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t xi : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedThirteenthDefect610 (Polynomial.C t)
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
          0 =
        Polynomial.C xi := by
  obtain ⟨t, lambda, _nu, xi0, ht, hHsq, hN, _hY, hZpow⟩ :=
    normalized610ScaleZero_exists_twelfthClearedDefect hsource
  have ht9 : (Polynomial.C t : k[X]) ^ 9 ≠ 0 :=
    pow_ne_zero 9 (Polynomial.C_ne_zero.mpr ht)
  have hlambda : lambda = 0 := by
    have hmul : Polynomial.C lambda * (Polynomial.C t) ^ 9 = 0 :=
      hN.symm.trans haligned
    have hC : Polynomial.C lambda = 0 :=
      (mul_eq_zero.mp hmul).resolve_right ht9
    exact Polynomial.C_eq_zero.mp hC
  refine ⟨t, xi0 * t ^ 65, ht, hHsq, ?_⟩
  have hZ :
      localClearedThirteenthDefect610 (Polynomial.C t)
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
          0 =
        Polynomial.C (xi0 * t ^ 65) := by
    rw [← hlambda, hZpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) xi0 (t ^ 65)).symm
  exact hZ


/-- Nonzero discriminator branch: `λ ≠ 0` and the weight-sixty-five
defect is still a ground constant. -/
theorem normalized610ScaleZero_twelfthClearedDefect_of_nonzero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0)
    (hnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5 *
            H ^ 2 -
        (3 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda xi : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5) *
            H ^ 2 -
        (3 : k[X]) *
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9) =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedThirteenthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C xi := by
  obtain ⟨t, lambda, _nu, xi0, ht, hHsq, hN, _hY, hZpow⟩ :=
    normalized610ScaleZero_exists_twelfthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro hzero
    apply hnonzero
    simpa only [hzero, Polynomial.C_0, zero_mul] using hN
  refine ⟨t, lambda, xi0 * t ^ 65, ht, hlambda, hHsq, hN, ?_⟩
  have hZ :
      localClearedThirteenthDefect610 (Polynomial.C t)
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
          lambda =
        Polynomial.C (xi0 * t ^ 65) := by
    rw [hZpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) xi0 (t ^ 65)).symm
  exact hZ

end ScaleZeroTwelfthDefect610

end Max11DegreeRoutes
