import Grok610ScaleZeroNinthDefectScratch

/-! # Scale-zero tenth cleared defect for the normalized `(6,10)`, `H = 0` leaf

Continuation of `Grok610ScaleZeroNinthDefectScratch` on the constant core
`H = (C t)²`.  The ninth packet already forces the discriminator `N` and
the weight-fifty defect `ι` to ground constants, including the exact
selector `18 q₀ h⁵⁰`.  This file consumes the next unused Keller
coefficient, the degree-`4` Jacobian row

```
(p₄)' (1 q₁) + (p₃)' (2 q₂) + (p₂)' (3 q₃) + (p₁)' (4 q₄) + (p₀)' (5 q₅)
  - (5 p₅) q₀' - (4 p₄) q₁' - (3 p₃) q₂' - (2 p₂) q₃' - (1 p₁) q₄' = 0
```

of the same monic depression.  After the sextic change that kills `z⁵`,
that row is
`5 S E' + 4 T D' + 3 U C' + 2 V B' + W A' - D T' - 2 C U' - 3 B V'
- 4 A W' = 0`.  The corresponding first integral `κ` clears to the
weight-fifty-five polynomial defect, and at scale zero that defect is
again a ground-field constant.

This file supersedes the unverified `Grok610ScaleZeroTenthDefectScratch`
attempt.  Its `κ` formula, weight-fifty-five clearing, and packet wiring
were re-derived independently and port unchanged; the derivation-in-zero
reduction is completed with the full constant-derivative kill set
(`d (385/31104) = 0` through `d (A⁵)`), whose absence left opaque
derivative atoms in the final `linear_combination`, and the aligned
`λ = 0` specialization states the literal `132`-monomial residue instead
of a reflexive identity.

The degree-`5` iota first integral and the exact `18 q₀ h⁵⁰` residual
are preserved and not cleared to zero.  No total-degree or twice-prime
theorem is used.  A constant scale has no finite root, so the scale-two
eleventh-face jet is unavailable.  Both the vanishing and the nonzero
constant branches of `λ` and of the weight-fifty and weight-fifty-five
defects are kept.  The packet does not close the leaf: unused Jacobian
coefficients start at degree `3`.
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

section ScaleZeroTenthDefect610

variable {k : Type*} [Field k] [CharZero k]

/-! ## Literal next Keller coefficient -/

set_option maxHeartbeats 64000000 in
/-- The eleventh row below the leading weighted-Wronskian row for outer
degrees `(6,10)`.  Unused Jacobian coefficients of the ninth packet
start at degree `4`. -/
theorem scaleZeroRaw_eleventhCoefficientJacobianRow_610 {K : Type*}
    [Field K] [CharZero K] {p q : K[X][Y]} {j : K}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j)) :
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : K)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : K)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : K)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : K)) -
      ((p.coeff 5 * Polynomial.C (5 : K)) * (q.coeff 0).derivative +
        (p.coeff 4 * Polynomial.C (4 : K)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : K)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : K)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) =
      0 := by
  have hcoeff := congrArg (fun r : K[X][Y] => r.coeff 4) hjac
  simp only [bivariateJacobian, Polynomial.coeff_sub, Polynomial.coeff_mul,
    coeff_xderiv, Polynomial.coeff_derivative, Polynomial.coeff_C,
    show (4 : ℕ) ≠ 0 by norm_num, ite_false] at hcoeff
  have hanti : (Finset.HasAntidiagonal.antidiagonal 4 :
      Finset (ℕ × ℕ)) =
      ({(0, 4), (1, 3), (2, 2), (3, 1),
        (4, 0)} : Finset (ℕ × ℕ)) := by decide
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
  rw [hC2, hC3, hC4, hC5]
  linear_combination hcoeff

set_option maxHeartbeats 64000000 in
/-- Source-facing degree-`4` Jacobian row of a normalized scale-zero
`(6,10)` pair. -/
theorem normalized610ScaleZero_eleventhCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : k)) -
      ((p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 0).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) =
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
    scaleZeroRaw_eleventhCoefficientJacobianRow_610 hp hq hjac

set_option maxHeartbeats 64000000 in
/-- At scale zero the common core is constant, so the leading sextic
coefficient of the degree-`4` row is a differential constant.  The row
itself has no `p₆'` term. -/
theorem scaleZero_eleventhCoefficientJacobianRow_610
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 6) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp6 : p.coeff 6 = H ^ 3) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : k)) -
      ((p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 0).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp6der : (p.coeff 6).derivative = 0 := by
    rw [hp6, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := scaleZeroRaw_eleventhCoefficientJacobianRow_610 hp hq hjac
  simpa [hp6der, hq10der] using hrow

set_option maxHeartbeats 64000000 in
/-- Source-facing scale-zero collapse of the degree-`4` row. -/
theorem normalized610ScaleZero_eleventhCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 4).derivative * q.coeff 1 +
        (p.coeff 3).derivative * (q.coeff 2 * Polynomial.C (2 : k)) +
        (p.coeff 2).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 1).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 0).derivative * (q.coeff 5 * Polynomial.C (5 : k)) -
      ((p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 0).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 1).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 2).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 3).derivative +
        p.coeff 1 * (q.coeff 4).derivative) =
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
    scaleZero_eleventhCoefficientJacobianRow_610 hp hq hjac hHdegree
      (by simpa only [p] using hp6) (by simpa only [q] using hq10)

/-! ## Weight-fifty-five cleared defect after a square root of the core -/

section Depression610Eleventh

variable {F : Type*} [Field F] [CharZero F]

set_option maxHeartbeats 64000000 in
/-- First residual of the degree-`4` row.  Equivalent to
`(1/6) A θ + (1/3) B η + (1/2) C ζ - (1/8) A² ζ + (2/3) D ε
- (2/9) A B ε + (5/6) E δ + (35/1296) A³ δ - (5/36) A C δ
- (5/72) B² δ + (20/243) A³ B α - (4/27) A² D α - (8/27) A B C α
- (4/81) B³ α + (4/9) B E α + (4/9) C D α + (385/31104) A⁴ β
- (35/432) A² C β - (35/432) A B² β + (7/36) A E β + (7/36) B D β
+ (7/72) C² β - (3/256) L A⁵ + (3/32) L A³ C + (9/64) L A² B²
- (3/16) L A² E - (3/8) L A B D - (3/16) L A C² - (3/16) L B² C
+ (3/4) L C E + (3/8) L D² - (35/729) A⁴ B + (20/243) A³ D
+ (20/81) A² B C + (20/243) A B³ - (10/27) A B E - (10/27) A C D
- (5/27) B² D - (5/27) B C² + (10/9) D E`
on the second- through ninth-face integrals. -/
def kappaResidual610
    (L A B C0 D0 E0 P Q R S0 T0 U0 V0 W0 : F) : F :=
  (1 / 6 : F) * A * thetaResidual610 L A B C0 D0 E0 P Q R S0 T0 U0 W0 +
    (1 / 3 : F) * B * etaResidual610 L A B C0 D0 E0 P Q R S0 T0 V0 +
    (1 / 2 : F) * C0 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 -
    (1 / 8 : F) * A ^ 2 * zetaResidual610 L A B C0 D0 E0 P Q R S0 U0 +
    (2 / 3 : F) * D0 * epsilonResidual610 L A B C0 D0 E0 P Q R T0 -
    (2 / 9 : F) * A * B * epsilonResidual610 L A B C0 D0 E0 P Q R T0 +
    (5 / 6 : F) * E0 * deltaResidual610 L A B C0 D0 P Q S0 +
    (35 / 1296 : F) * A ^ 3 * deltaResidual610 L A B C0 D0 P Q S0 -
    (5 / 36 : F) * A * C0 * deltaResidual610 L A B C0 D0 P Q S0 -
    (5 / 72 : F) * B ^ 2 * deltaResidual610 L A B C0 D0 P Q S0 +
    (20 / 243 : F) * A ^ 3 * B * alphaResidual610 A P -
    (4 / 27 : F) * A ^ 2 * D0 * alphaResidual610 A P -
    (8 / 27 : F) * A * B * C0 * alphaResidual610 A P -
    (4 / 81 : F) * B ^ 3 * alphaResidual610 A P +
    (4 / 9 : F) * B * E0 * alphaResidual610 A P +
    (4 / 9 : F) * C0 * D0 * alphaResidual610 A P +
    (385 / 31104 : F) * A ^ 4 * betaResidual610 L A B Q -
    (35 / 432 : F) * A ^ 2 * C0 * betaResidual610 L A B Q -
    (35 / 432 : F) * A * B ^ 2 * betaResidual610 L A B Q +
    (7 / 36 : F) * A * E0 * betaResidual610 L A B Q +
    (7 / 36 : F) * B * D0 * betaResidual610 L A B Q +
    (7 / 72 : F) * C0 ^ 2 * betaResidual610 L A B Q -
    (3 / 256 : F) * L * A ^ 5 +
    (3 / 32 : F) * L * A ^ 3 * C0 +
    (9 / 64 : F) * L * A ^ 2 * B ^ 2 -
    (3 / 16 : F) * L * A ^ 2 * E0 -
    (3 / 8 : F) * L * A * B * D0 -
    (3 / 16 : F) * L * A * C0 ^ 2 -
    (3 / 16 : F) * L * B ^ 2 * C0 +
    (3 / 4 : F) * L * C0 * E0 +
    (3 / 8 : F) * L * D0 ^ 2 -
    (35 / 729 : F) * A ^ 4 * B +
    (20 / 243 : F) * A ^ 3 * D0 +
    (20 / 81 : F) * A ^ 2 * B * C0 +
    (20 / 243 : F) * A * B ^ 3 -
    (10 / 27 : F) * A * B * E0 -
    (10 / 27 : F) * A * C0 * D0 -
    (5 / 27 : F) * B ^ 2 * D0 -
    (5 / 27 : F) * B * C0 ^ 2 +
    (10 / 9 : F) * D0 * E0

-- Fix the carrier of the standard operations before elaborating this arithmetic tree.
local infixl:65 (priority := high) " + " => (HAdd.hAdd (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:65 (priority := high) " - " => (HSub.hSub (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:70 (priority := high) " * " => (HMul.hMul (α := F[X]) (β := F[X]) (γ := F[X]))
local infixl:70 (priority := high) " / " => (HDiv.hDiv (α := F[X]) (β := F[X]) (γ := F[X]))
local infixr:80 (priority := high) " ^ " => (HPow.hPow (α := F[X]) (β := Nat) (γ := F[X]))
local prefix:75 (priority := high) "-" => (Neg.neg (α := F[X]))

set_option maxHeartbeats 64000000 in
/-- Polynomial numerator of `3761479876608 h⁵⁵ κ` on the ninth-power face. -/
def localClearedEleventhDefect610
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) (lambda : F) : F[X] :=
    - (231612681800 : F[X]) * a5 ^ 11
    + (114648277491 : F[X]) * a5 ^ 10 * h ^ 5 * Polynomial.C lambda
    + (2018963377200 : F[X]) * a4 * a5 ^ 9 * h ^ 6
    + (346108007520 : F[X]) * a5 ^ 9 * b8 * h ^ 2
    - (1168114525380 : F[X]) * a4 * a5 ^ 8 * h ^ 11 * Polynomial.C lambda
    - (2071125045000 : F[X]) * a3 * a5 ^ 8 * h ^ 12
    - (347949007560 : F[X]) * a5 ^ 8 * b7 * h ^ 8
    - (5302080115200 : F[X]) * a4 ^ 2 * a5 ^ 7 * h ^ 12
    - (3181248069120 : F[X]) * a4 * a5 ^ 7 * b8 * h ^ 8
    + (1192968025920 : F[X]) * a3 * a5 ^ 7 * h ^ 17 * Polynomial.C lambda
    + (2133763948800 : F[X]) * a2 * a5 ^ 7 * h ^ 18
    + (349161373440 : F[X]) * a5 ^ 7 * b6 * h ^ 14
    + (4175388090720 : F[X]) * a4 ^ 2 * a5 ^ 6 * h ^ 17 * Polynomial.C lambda
    + (8826023606400 : F[X]) * a3 * a4 * a5 ^ 6 * h ^ 18
    + (2851484549760 : F[X]) * a4 * a5 ^ 6 * b7 * h ^ 14
    + (3258839485440 : F[X]) * a3 * a5 ^ 6 * b8 * h ^ 14
    - (1222064807040 : F[X]) * a2 * a5 ^ 6 * h ^ 23 * Polynomial.C lambda
    - (2211355365120 : F[X]) * a1 * a5 ^ 6 * h ^ 24
    - (349161373440 : F[X]) * a5 ^ 6 * b5 * h ^ 20
    + (2715699571200 : F[X]) * a4 ^ 3 * a5 ^ 5 * h ^ 18
    + (9776518456320 : F[X]) * a4 ^ 2 * a5 ^ 5 * b8 * h ^ 14
    - (7332388842240 : F[X]) * a3 * a4 * a5 ^ 5 * h ^ 23 * Polynomial.C lambda
    - (6983227468800 : F[X]) * a2 * a4 * a5 ^ 5 * h ^ 24
    - (2513961888768 : F[X]) * a4 * a5 ^ 5 * b6 * h ^ 20
    - (3491613734400 : F[X]) * a3 ^ 2 * a5 ^ 5 * h ^ 24
    - (2932955536896 : F[X]) * a3 * a5 ^ 5 * b7 * h ^ 20
    - (3351949185024 : F[X]) * a2 * a5 ^ 5 * b8 * h ^ 20
    + (1256980944384 : F[X]) * a1 * a5 ^ 5 * h ^ 29 * Polynomial.C lambda
    + (2311689093120 : F[X]) * a0 * a5 ^ 5 * h ^ 30
    + (346753363968 : F[X]) * a5 ^ 5 * b4 * h ^ 26
    - (6110324035200 : F[X]) * a4 ^ 3 * a5 ^ 4 * h ^ 23 * Polynomial.C lambda
    - (1745806867200 : F[X]) * a3 * a4 ^ 2 * a5 ^ 4 * h ^ 24
    - (7332388842240 : F[X]) * a4 ^ 2 * a5 ^ 4 * b7 * h ^ 20
    - (16759745925120 : F[X]) * a3 * a4 * a5 ^ 4 * b8 * h ^ 20
    + (6284904721920 : F[X]) * a2 * a4 * a5 ^ 4 * h ^ 29 * Polynomial.C lambda
    + (5056819891200 : F[X]) * a1 * a4 * a5 ^ 4 * h ^ 30
    + (2167208524800 : F[X]) * a4 * a5 ^ 4 * b5 * h ^ 26
    + (3142452360960 : F[X]) * a3 ^ 2 * a5 ^ 4 * h ^ 29 * Polynomial.C lambda
    + (5056819891200 : F[X]) * a2 * a3 * a5 ^ 4 * h ^ 30
    + (2600650229760 : F[X]) * a3 * a5 ^ 4 * b6 * h ^ 26
    + (3034091934720 : F[X]) * a2 * a5 ^ 4 * b7 * h ^ 26
    + (3467533639680 : F[X]) * a1 * a5 ^ 4 * b8 * h ^ 26
    - (1300325114880 : F[X]) * a0 * a5 ^ 4 * h ^ 35 * Polynomial.C lambda
    - (339215247360 : F[X]) * a5 ^ 4 * b3 * h ^ 32
    + (4655484979200 : F[X]) * a4 ^ 4 * a5 ^ 3 * h ^ 24
    - (11173163950080 : F[X]) * a4 ^ 3 * a5 ^ 3 * b8 * h ^ 20
    + (12569809443840 : F[X]) * a3 * a4 ^ 2 * a5 ^ 3 * h ^ 29 * Polynomial.C lambda
    - (2889611366400 : F[X]) * a2 * a4 ^ 2 * a5 ^ 3 * h ^ 30
    + (5201300459520 : F[X]) * a4 ^ 2 * a5 ^ 3 * b6 * h ^ 26
    - (2889611366400 : F[X]) * a3 ^ 2 * a4 * a5 ^ 3 * h ^ 30
    + (12136367738880 : F[X]) * a3 * a4 * a5 ^ 3 * b7 * h ^ 26
    + (13870134558720 : F[X]) * a2 * a4 * a5 ^ 3 * b8 * h ^ 26
    - (5201300459520 : F[X]) * a1 * a4 * a5 ^ 3 * h ^ 35 * Polynomial.C lambda
    - (3015246643200 : F[X]) * a0 * a4 * a5 ^ 3 * h ^ 36
    - (1809147985920 : F[X]) * a4 * a5 ^ 3 * b4 * h ^ 32
    + (6935067279360 : F[X]) * a3 ^ 2 * a5 ^ 3 * b8 * h ^ 26
    - (5201300459520 : F[X]) * a2 * a3 * a5 ^ 3 * h ^ 35 * Polynomial.C lambda
    - (3015246643200 : F[X]) * a1 * a3 * a5 ^ 3 * h ^ 36
    - (2261434982400 : F[X]) * a3 * a5 ^ 3 * b5 * h ^ 32
    - (1507623321600 : F[X]) * a2 ^ 2 * a5 ^ 3 * h ^ 36
    - (2713721978880 : F[X]) * a2 * a5 ^ 3 * b6 * h ^ 32
    - (3166008975360 : F[X]) * a1 * a5 ^ 3 * b7 * h ^ 32
    - (3618295971840 : F[X]) * a0 * a5 ^ 3 * b8 * h ^ 32
    + (319261409280 : F[X]) * a5 ^ 3 * b2 * h ^ 38
    + (3142452360960 : F[X]) * a4 ^ 4 * a5 ^ 2 * h ^ 29 * Polynomial.C lambda
    - (15892862515200 : F[X]) * a3 * a4 ^ 3 * a5 ^ 2 * h ^ 30
    + (6068183869440 : F[X]) * a4 ^ 3 * a5 ^ 2 * b7 * h ^ 26
    + (20805201838080 : F[X]) * a3 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 26
    - (7801950689280 : F[X]) * a2 * a4 ^ 2 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    + (5653587456000 : F[X]) * a1 * a4 ^ 2 * a5 ^ 2 * h ^ 36
    - (3392152473600 : F[X]) * a4 ^ 2 * a5 ^ 2 * b5 * h ^ 32
    - (7801950689280 : F[X]) * a3 ^ 2 * a4 * a5 ^ 2 * h ^ 35 * Polynomial.C lambda
    + (11307174912000 : F[X]) * a2 * a3 * a4 * a5 ^ 2 * h ^ 36
    - (8141165936640 : F[X]) * a3 * a4 * a5 ^ 2 * b6 * h ^ 32
    - (9498026926080 : F[X]) * a2 * a4 * a5 ^ 2 * b7 * h ^ 32
    - (10854887915520 : F[X]) * a1 * a4 * a5 ^ 2 * b8 * h ^ 32
    + (4070582968320 : F[X]) * a0 * a4 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda
    + (1436676341760 : F[X]) * a4 * a5 ^ 2 * b3 * h ^ 38
    + (1884529152000 : F[X]) * a3 ^ 3 * a5 ^ 2 * h ^ 36
    - (4749013463040 : F[X]) * a3 ^ 2 * a5 ^ 2 * b7 * h ^ 32
    - (10854887915520 : F[X]) * a2 * a3 * a5 ^ 2 * b8 * h ^ 32
    + (4070582968320 : F[X]) * a1 * a3 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda
    + (798153523200 : F[X]) * a0 * a3 * a5 ^ 2 * h ^ 42
    + (1915568455680 : F[X]) * a3 * a5 ^ 2 * b4 * h ^ 38
    + (2035291484160 : F[X]) * a2 ^ 2 * a5 ^ 2 * h ^ 41 * Polynomial.C lambda
    + (798153523200 : F[X]) * a1 * a2 * a5 ^ 2 * h ^ 42
    + (2394460569600 : F[X]) * a2 * a5 ^ 2 * b5 * h ^ 38
    + (2873352683520 : F[X]) * a1 * a5 ^ 2 * b6 * h ^ 38
    + (3352244797440 : F[X]) * a0 * a5 ^ 2 * b7 * h ^ 38
    - (261213880320 : F[X]) * a5 ^ 2 * b1 * h ^ 44
    - (2889611366400 : F[X]) * a4 ^ 5 * a5 * h ^ 30
    + (3467533639680 : F[X]) * a4 ^ 4 * a5 * b8 * h ^ 26
    - (5201300459520 : F[X]) * a3 * a4 ^ 3 * a5 * h ^ 35 * Polynomial.C lambda
    + (10553363251200 : F[X]) * a2 * a4 ^ 3 * a5 * h ^ 36
    - (2713721978880 : F[X]) * a4 ^ 3 * a5 * b6 * h ^ 32
    + (15830044876800 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 * h ^ 36
    - (9498026926080 : F[X]) * a3 * a4 ^ 2 * a5 * b7 * h ^ 32
    - (10854887915520 : F[X]) * a2 * a4 ^ 2 * a5 * b8 * h ^ 32
    + (4070582968320 : F[X]) * a1 * a4 ^ 2 * a5 * h ^ 41 * Polynomial.C lambda
    - (6385228185600 : F[X]) * a0 * a4 ^ 2 * a5 * h ^ 42
    + (1915568455680 : F[X]) * a4 ^ 2 * a5 * b4 * h ^ 38
    - (10854887915520 : F[X]) * a3 ^ 2 * a4 * a5 * b8 * h ^ 32
    + (8141165936640 : F[X]) * a2 * a3 * a4 * a5 * h ^ 41 * Polynomial.C lambda
    - (12770456371200 : F[X]) * a1 * a3 * a4 * a5 * h ^ 42
    + (4788921139200 : F[X]) * a3 * a4 * a5 * b5 * h ^ 38
    - (6385228185600 : F[X]) * a2 ^ 2 * a4 * a5 * h ^ 42
    + (5746705367040 : F[X]) * a2 * a4 * a5 * b6 * h ^ 38
    + (6704489594880 : F[X]) * a1 * a4 * a5 * b7 * h ^ 38
    + (7662273822720 : F[X]) * a0 * a4 * a5 * b8 * h ^ 38
    - (1044855521280 : F[X]) * a4 * a5 * b2 * h ^ 44
    + (1356860989440 : F[X]) * a3 ^ 3 * a5 * h ^ 41 * Polynomial.C lambda
    - (6385228185600 : F[X]) * a2 * a3 ^ 2 * a5 * h ^ 42
    + (2873352683520 : F[X]) * a3 ^ 2 * a5 * b6 * h ^ 38
    + (6704489594880 : F[X]) * a2 * a3 * a5 * b7 * h ^ 38
    + (7662273822720 : F[X]) * a1 * a3 * a5 * b8 * h ^ 38
    - (2873352683520 : F[X]) * a0 * a3 * a5 * h ^ 47 * Polynomial.C lambda
    - (1567283281920 : F[X]) * a3 * a5 * b3 * h ^ 44
    + (3831136911360 : F[X]) * a2 ^ 2 * a5 * b8 * h ^ 38
    - (2873352683520 : F[X]) * a1 * a2 * a5 * h ^ 47 * Polynomial.C lambda
    + (1741425868800 : F[X]) * a0 * a2 * a5 * h ^ 48
    - (2089711042560 : F[X]) * a2 * a5 * b4 * h ^ 44
    + (870712934400 : F[X]) * a1 ^ 2 * a5 * h ^ 48
    - (2612138803200 : F[X]) * a1 * a5 * b5 * h ^ 44
    - (3134566563840 : F[X]) * a0 * a5 * b6 * h ^ 44
    - (260065022976 : F[X]) * a4 ^ 5 * h ^ 35 * Polynomial.C lambda
    + (4334417049600 : F[X]) * a3 * a4 ^ 4 * h ^ 36
    - (791502243840 : F[X]) * a4 ^ 4 * b7 * h ^ 32
    - (3618295971840 : F[X]) * a3 * a4 ^ 3 * b8 * h ^ 32
    + (1356860989440 : F[X]) * a2 * a4 ^ 3 * h ^ 41 * Polynomial.C lambda
    - (4522869964800 : F[X]) * a1 * a4 ^ 3 * h ^ 42
    + (798153523200 : F[X]) * a4 ^ 3 * b5 * h ^ 38
    + (2035291484160 : F[X]) * a3 ^ 2 * a4 ^ 2 * h ^ 41 * Polynomial.C lambda
    - (13568609894400 : F[X]) * a2 * a3 * a4 ^ 2 * h ^ 42
    + (2873352683520 : F[X]) * a3 * a4 ^ 2 * b6 * h ^ 38
    + (3352244797440 : F[X]) * a2 * a4 ^ 2 * b7 * h ^ 38
    + (3831136911360 : F[X]) * a1 * a4 ^ 2 * b8 * h ^ 38
    - (1436676341760 : F[X]) * a0 * a4 ^ 2 * h ^ 47 * Polynomial.C lambda
    - (783641640960 : F[X]) * a4 ^ 2 * b3 * h ^ 44
    - (4522869964800 : F[X]) * a3 ^ 3 * a4 * h ^ 42
    + (3352244797440 : F[X]) * a3 ^ 2 * a4 * b7 * h ^ 38
    + (7662273822720 : F[X]) * a2 * a3 * a4 * b8 * h ^ 38
    - (2873352683520 : F[X]) * a1 * a3 * a4 * h ^ 47 * Polynomial.C lambda
    + (9577842278400 : F[X]) * a0 * a3 * a4 * h ^ 48
    - (2089711042560 : F[X]) * a3 * a4 * b4 * h ^ 44
    - (1436676341760 : F[X]) * a2 ^ 2 * a4 * h ^ 47 * Polynomial.C lambda
    + (9577842278400 : F[X]) * a1 * a2 * a4 * h ^ 48
    - (2612138803200 : F[X]) * a2 * a4 * b5 * h ^ 44
    - (3134566563840 : F[X]) * a1 * a4 * b6 * h ^ 44
    - (3656994324480 : F[X]) * a0 * a4 * b7 * h ^ 44
    + (626913312768 : F[X]) * a4 * b1 * h ^ 50
    + (1277045637120 : F[X]) * a3 ^ 3 * b8 * h ^ 38
    - (1436676341760 : F[X]) * a2 * a3 ^ 2 * h ^ 47 * Polynomial.C lambda
    + (4788921139200 : F[X]) * a1 * a3 ^ 2 * h ^ 48
    - (1306069401600 : F[X]) * a3 ^ 2 * b5 * h ^ 44
    + (4788921139200 : F[X]) * a2 ^ 2 * a3 * h ^ 48
    - (3134566563840 : F[X]) * a2 * a3 * b6 * h ^ 44
    - (3656994324480 : F[X]) * a1 * a3 * b7 * h ^ 44
    - (4179422085120 : F[X]) * a0 * a3 * b8 * h ^ 44
    + (1253826625536 : F[X]) * a3 * b2 * h ^ 50
    - (1828497162240 : F[X]) * a2 ^ 2 * b7 * h ^ 44
    - (4179422085120 : F[X]) * a1 * a2 * b8 * h ^ 44
    + (1567283281920 : F[X]) * a0 * a2 * h ^ 53 * Polynomial.C lambda
    + (1880739938304 : F[X]) * a2 * b3 * h ^ 50
    + (783641640960 : F[X]) * a1 ^ 2 * h ^ 53 * Polynomial.C lambda
    - (5224277606400 : F[X]) * a0 * a1 * h ^ 54
    + (2507653251072 : F[X]) * a1 * b4 * h ^ 50
    + (3134566563840 : F[X]) * a0 * b5 * h ^ 50

set_option maxHeartbeats 64000000 in
/-- Aligned specialization of the weight-fifty-five defect: the
`λ`-monomials drop. -/
theorem localClearedEleventhDefect610_of_lambda_zero
    (h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3 b2 b1 : F[X]) :
    localClearedEleventhDefect610 h a5 a4 a3 a2 a1 a0 b8 b7 b6 b5 b4 b3
        b2 b1 0 =
    - (231612681800 : F[X]) * a5 ^ 11
    + (2018963377200 : F[X]) * a4 * a5 ^ 9 * h ^ 6
    + (346108007520 : F[X]) * a5 ^ 9 * b8 * h ^ 2
    - (2071125045000 : F[X]) * a3 * a5 ^ 8 * h ^ 12
    - (347949007560 : F[X]) * a5 ^ 8 * b7 * h ^ 8
    - (5302080115200 : F[X]) * a4 ^ 2 * a5 ^ 7 * h ^ 12
    - (3181248069120 : F[X]) * a4 * a5 ^ 7 * b8 * h ^ 8
    + (2133763948800 : F[X]) * a2 * a5 ^ 7 * h ^ 18
    + (349161373440 : F[X]) * a5 ^ 7 * b6 * h ^ 14
    + (8826023606400 : F[X]) * a3 * a4 * a5 ^ 6 * h ^ 18
    + (2851484549760 : F[X]) * a4 * a5 ^ 6 * b7 * h ^ 14
    + (3258839485440 : F[X]) * a3 * a5 ^ 6 * b8 * h ^ 14
    - (2211355365120 : F[X]) * a1 * a5 ^ 6 * h ^ 24
    - (349161373440 : F[X]) * a5 ^ 6 * b5 * h ^ 20
    + (2715699571200 : F[X]) * a4 ^ 3 * a5 ^ 5 * h ^ 18
    + (9776518456320 : F[X]) * a4 ^ 2 * a5 ^ 5 * b8 * h ^ 14
    - (6983227468800 : F[X]) * a2 * a4 * a5 ^ 5 * h ^ 24
    - (2513961888768 : F[X]) * a4 * a5 ^ 5 * b6 * h ^ 20
    - (3491613734400 : F[X]) * a3 ^ 2 * a5 ^ 5 * h ^ 24
    - (2932955536896 : F[X]) * a3 * a5 ^ 5 * b7 * h ^ 20
    - (3351949185024 : F[X]) * a2 * a5 ^ 5 * b8 * h ^ 20
    + (2311689093120 : F[X]) * a0 * a5 ^ 5 * h ^ 30
    + (346753363968 : F[X]) * a5 ^ 5 * b4 * h ^ 26
    - (1745806867200 : F[X]) * a3 * a4 ^ 2 * a5 ^ 4 * h ^ 24
    - (7332388842240 : F[X]) * a4 ^ 2 * a5 ^ 4 * b7 * h ^ 20
    - (16759745925120 : F[X]) * a3 * a4 * a5 ^ 4 * b8 * h ^ 20
    + (5056819891200 : F[X]) * a1 * a4 * a5 ^ 4 * h ^ 30
    + (2167208524800 : F[X]) * a4 * a5 ^ 4 * b5 * h ^ 26
    + (5056819891200 : F[X]) * a2 * a3 * a5 ^ 4 * h ^ 30
    + (2600650229760 : F[X]) * a3 * a5 ^ 4 * b6 * h ^ 26
    + (3034091934720 : F[X]) * a2 * a5 ^ 4 * b7 * h ^ 26
    + (3467533639680 : F[X]) * a1 * a5 ^ 4 * b8 * h ^ 26
    - (339215247360 : F[X]) * a5 ^ 4 * b3 * h ^ 32
    + (4655484979200 : F[X]) * a4 ^ 4 * a5 ^ 3 * h ^ 24
    - (11173163950080 : F[X]) * a4 ^ 3 * a5 ^ 3 * b8 * h ^ 20
    - (2889611366400 : F[X]) * a2 * a4 ^ 2 * a5 ^ 3 * h ^ 30
    + (5201300459520 : F[X]) * a4 ^ 2 * a5 ^ 3 * b6 * h ^ 26
    - (2889611366400 : F[X]) * a3 ^ 2 * a4 * a5 ^ 3 * h ^ 30
    + (12136367738880 : F[X]) * a3 * a4 * a5 ^ 3 * b7 * h ^ 26
    + (13870134558720 : F[X]) * a2 * a4 * a5 ^ 3 * b8 * h ^ 26
    - (3015246643200 : F[X]) * a0 * a4 * a5 ^ 3 * h ^ 36
    - (1809147985920 : F[X]) * a4 * a5 ^ 3 * b4 * h ^ 32
    + (6935067279360 : F[X]) * a3 ^ 2 * a5 ^ 3 * b8 * h ^ 26
    - (3015246643200 : F[X]) * a1 * a3 * a5 ^ 3 * h ^ 36
    - (2261434982400 : F[X]) * a3 * a5 ^ 3 * b5 * h ^ 32
    - (1507623321600 : F[X]) * a2 ^ 2 * a5 ^ 3 * h ^ 36
    - (2713721978880 : F[X]) * a2 * a5 ^ 3 * b6 * h ^ 32
    - (3166008975360 : F[X]) * a1 * a5 ^ 3 * b7 * h ^ 32
    - (3618295971840 : F[X]) * a0 * a5 ^ 3 * b8 * h ^ 32
    + (319261409280 : F[X]) * a5 ^ 3 * b2 * h ^ 38
    - (15892862515200 : F[X]) * a3 * a4 ^ 3 * a5 ^ 2 * h ^ 30
    + (6068183869440 : F[X]) * a4 ^ 3 * a5 ^ 2 * b7 * h ^ 26
    + (20805201838080 : F[X]) * a3 * a4 ^ 2 * a5 ^ 2 * b8 * h ^ 26
    + (5653587456000 : F[X]) * a1 * a4 ^ 2 * a5 ^ 2 * h ^ 36
    - (3392152473600 : F[X]) * a4 ^ 2 * a5 ^ 2 * b5 * h ^ 32
    + (11307174912000 : F[X]) * a2 * a3 * a4 * a5 ^ 2 * h ^ 36
    - (8141165936640 : F[X]) * a3 * a4 * a5 ^ 2 * b6 * h ^ 32
    - (9498026926080 : F[X]) * a2 * a4 * a5 ^ 2 * b7 * h ^ 32
    - (10854887915520 : F[X]) * a1 * a4 * a5 ^ 2 * b8 * h ^ 32
    + (1436676341760 : F[X]) * a4 * a5 ^ 2 * b3 * h ^ 38
    + (1884529152000 : F[X]) * a3 ^ 3 * a5 ^ 2 * h ^ 36
    - (4749013463040 : F[X]) * a3 ^ 2 * a5 ^ 2 * b7 * h ^ 32
    - (10854887915520 : F[X]) * a2 * a3 * a5 ^ 2 * b8 * h ^ 32
    + (798153523200 : F[X]) * a0 * a3 * a5 ^ 2 * h ^ 42
    + (1915568455680 : F[X]) * a3 * a5 ^ 2 * b4 * h ^ 38
    + (798153523200 : F[X]) * a1 * a2 * a5 ^ 2 * h ^ 42
    + (2394460569600 : F[X]) * a2 * a5 ^ 2 * b5 * h ^ 38
    + (2873352683520 : F[X]) * a1 * a5 ^ 2 * b6 * h ^ 38
    + (3352244797440 : F[X]) * a0 * a5 ^ 2 * b7 * h ^ 38
    - (261213880320 : F[X]) * a5 ^ 2 * b1 * h ^ 44
    - (2889611366400 : F[X]) * a4 ^ 5 * a5 * h ^ 30
    + (3467533639680 : F[X]) * a4 ^ 4 * a5 * b8 * h ^ 26
    + (10553363251200 : F[X]) * a2 * a4 ^ 3 * a5 * h ^ 36
    - (2713721978880 : F[X]) * a4 ^ 3 * a5 * b6 * h ^ 32
    + (15830044876800 : F[X]) * a3 ^ 2 * a4 ^ 2 * a5 * h ^ 36
    - (9498026926080 : F[X]) * a3 * a4 ^ 2 * a5 * b7 * h ^ 32
    - (10854887915520 : F[X]) * a2 * a4 ^ 2 * a5 * b8 * h ^ 32
    - (6385228185600 : F[X]) * a0 * a4 ^ 2 * a5 * h ^ 42
    + (1915568455680 : F[X]) * a4 ^ 2 * a5 * b4 * h ^ 38
    - (10854887915520 : F[X]) * a3 ^ 2 * a4 * a5 * b8 * h ^ 32
    - (12770456371200 : F[X]) * a1 * a3 * a4 * a5 * h ^ 42
    + (4788921139200 : F[X]) * a3 * a4 * a5 * b5 * h ^ 38
    - (6385228185600 : F[X]) * a2 ^ 2 * a4 * a5 * h ^ 42
    + (5746705367040 : F[X]) * a2 * a4 * a5 * b6 * h ^ 38
    + (6704489594880 : F[X]) * a1 * a4 * a5 * b7 * h ^ 38
    + (7662273822720 : F[X]) * a0 * a4 * a5 * b8 * h ^ 38
    - (1044855521280 : F[X]) * a4 * a5 * b2 * h ^ 44
    - (6385228185600 : F[X]) * a2 * a3 ^ 2 * a5 * h ^ 42
    + (2873352683520 : F[X]) * a3 ^ 2 * a5 * b6 * h ^ 38
    + (6704489594880 : F[X]) * a2 * a3 * a5 * b7 * h ^ 38
    + (7662273822720 : F[X]) * a1 * a3 * a5 * b8 * h ^ 38
    - (1567283281920 : F[X]) * a3 * a5 * b3 * h ^ 44
    + (3831136911360 : F[X]) * a2 ^ 2 * a5 * b8 * h ^ 38
    + (1741425868800 : F[X]) * a0 * a2 * a5 * h ^ 48
    - (2089711042560 : F[X]) * a2 * a5 * b4 * h ^ 44
    + (870712934400 : F[X]) * a1 ^ 2 * a5 * h ^ 48
    - (2612138803200 : F[X]) * a1 * a5 * b5 * h ^ 44
    - (3134566563840 : F[X]) * a0 * a5 * b6 * h ^ 44
    + (4334417049600 : F[X]) * a3 * a4 ^ 4 * h ^ 36
    - (791502243840 : F[X]) * a4 ^ 4 * b7 * h ^ 32
    - (3618295971840 : F[X]) * a3 * a4 ^ 3 * b8 * h ^ 32
    - (4522869964800 : F[X]) * a1 * a4 ^ 3 * h ^ 42
    + (798153523200 : F[X]) * a4 ^ 3 * b5 * h ^ 38
    - (13568609894400 : F[X]) * a2 * a3 * a4 ^ 2 * h ^ 42
    + (2873352683520 : F[X]) * a3 * a4 ^ 2 * b6 * h ^ 38
    + (3352244797440 : F[X]) * a2 * a4 ^ 2 * b7 * h ^ 38
    + (3831136911360 : F[X]) * a1 * a4 ^ 2 * b8 * h ^ 38
    - (783641640960 : F[X]) * a4 ^ 2 * b3 * h ^ 44
    - (4522869964800 : F[X]) * a3 ^ 3 * a4 * h ^ 42
    + (3352244797440 : F[X]) * a3 ^ 2 * a4 * b7 * h ^ 38
    + (7662273822720 : F[X]) * a2 * a3 * a4 * b8 * h ^ 38
    + (9577842278400 : F[X]) * a0 * a3 * a4 * h ^ 48
    - (2089711042560 : F[X]) * a3 * a4 * b4 * h ^ 44
    + (9577842278400 : F[X]) * a1 * a2 * a4 * h ^ 48
    - (2612138803200 : F[X]) * a2 * a4 * b5 * h ^ 44
    - (3134566563840 : F[X]) * a1 * a4 * b6 * h ^ 44
    - (3656994324480 : F[X]) * a0 * a4 * b7 * h ^ 44
    + (626913312768 : F[X]) * a4 * b1 * h ^ 50
    + (1277045637120 : F[X]) * a3 ^ 3 * b8 * h ^ 38
    + (4788921139200 : F[X]) * a1 * a3 ^ 2 * h ^ 48
    - (1306069401600 : F[X]) * a3 ^ 2 * b5 * h ^ 44
    + (4788921139200 : F[X]) * a2 ^ 2 * a3 * h ^ 48
    - (3134566563840 : F[X]) * a2 * a3 * b6 * h ^ 44
    - (3656994324480 : F[X]) * a1 * a3 * b7 * h ^ 44
    - (4179422085120 : F[X]) * a0 * a3 * b8 * h ^ 44
    + (1253826625536 : F[X]) * a3 * b2 * h ^ 50
    - (1828497162240 : F[X]) * a2 ^ 2 * b7 * h ^ 44
    - (4179422085120 : F[X]) * a1 * a2 * b8 * h ^ 44
    + (1880739938304 : F[X]) * a2 * b3 * h ^ 50
    - (5224277606400 : F[X]) * a0 * a1 * h ^ 54
    + (2507653251072 : F[X]) * a1 * b4 * h ^ 50
    + (3134566563840 : F[X]) * a0 * b5 * h ^ 50 := by
  simp [localClearedEleventhDefect610, map_zero]


end Depression610Eleventh

end ScaleZeroTenthDefect610
end Max11DegreeRoutes
end
