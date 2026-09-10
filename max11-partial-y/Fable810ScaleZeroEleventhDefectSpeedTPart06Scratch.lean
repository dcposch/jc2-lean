import Fable810ScaleZeroEleventhDefectSpeedTPart05Scratch

/-! # Scale-zero eleventh defect for the normalized `(8,10)`, `H = 0` leaf

The tenth-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first ten octic/decic defects to ground constants times `h¹⁴`, `h²¹`,
`h²⁸`, `h³⁵`, `h⁴²`, `h⁴⁹`, `h⁵⁶`, `h⁶³`, `h⁷⁰`, and `h⁷⁷`.  This file
consumes the next unused Keller coefficient of the same monic
octic-decic depression: the degree-`5` Jacobian row is
`6 R G' + 5 S F' + 4 T E' + 3 U D' + 2 V C' + W B'
- F S' - 2 E T' - 3 D U' - 4 C V' - 5 B W' - 6 A X' = 0`.  The
corresponding twelfth cleared polynomial defect of weight eighty-four
is likewise a ground-field constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  The same zero/nonzero split is recorded
for the weight-`84` defect itself.  Root-evaluation from a scale-two
face is unavailable, because a nonzero constant has no finite root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`4` residual of
the same monic depression.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000

/-! ## Literal next Keller coefficient -/

section ScaleZeroEleventhDefect810

variable {k : Type*} [Field k] [CharZero k]

set_option linter.unusedSectionVars false

/-! ## Degree-`5` source Jacobian row -/

set_option maxHeartbeats 64000000 in
/-- Source-facing degree-`5` Jacobian row of a normalized scale-zero
`(8,10)` pair. -/
theorem normalized810ScaleZero_twelfthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
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
    ⟨_hH, _hHdegree, hPdegree, hQdegree, _hp8, _hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using fableScaleZero_twelfthCoefficientJacobianRow_raw_810 hp hq hjac

set_option maxHeartbeats 64000000 in
/-- At scale zero the common core is constant, so the leading octic
coefficient of the degree-`5` row is a differential constant. -/
theorem scaleZero_twelfthCoefficientJacobianRow_810
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
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
  have hrow := fableScaleZero_twelfthCoefficientJacobianRow_raw_810 hp hq hjac
  simpa using hrow

set_option maxHeartbeats 64000000 in
/-- Source-facing scale-zero collapse of the degree-`5` row. -/
theorem normalized810ScaleZero_twelfthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
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
    ⟨_hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  simpa only [p, q] using
    scaleZero_twelfthCoefficientJacobianRow_810 hp hq hjac hHdegree
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)

/-! ## Degree-`5` monic Jacobian row -/

set_option maxHeartbeats 64000000 in
/-- For a monic octic and a monic decic whose `z⁹` coefficient `L` is
already a differential constant, the degree-`5` Jacobian coefficient
is exactly
`6 R G' + 5 S F' + 4 T E' + 3 U D' + 2 V C' + W B'
- F S' - 2 E T' - 3 D U' - 4 C V' - 5 B W' - 6 A X'`.
Here `A = f.coeff 6`, `B = f.coeff 5`, `C = f.coeff 4`, `D = f.coeff 3`,
`E = f.coeff 2`, `F = f.coeff 1`, `G = f.coeff 0`, `L = g.coeff 9`,
`P = g.coeff 8`, `Q = g.coeff 7`, `R = g.coeff 6`, `S = g.coeff 5`,
`T = g.coeff 4`, `U = g.coeff 3`, `V = g.coeff 2`, `W = g.coeff 1`,
and `X = g.coeff 0`. -/
theorem scaleZero_monicOcticDecic_degree5Row_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 5 =
      (6 : F) * g.coeff 6 * d (f.coeff 0) +
        (5 : F) * g.coeff 5 * d (f.coeff 1) +
        (4 : F) * g.coeff 4 * d (f.coeff 2) +
        (3 : F) * g.coeff 3 * d (f.coeff 3) +
        (2 : F) * g.coeff 2 * d (f.coeff 4) +
        g.coeff 1 * d (f.coeff 5) -
          f.coeff 1 * d (g.coeff 5) -
          (2 : F) * f.coeff 2 * d (g.coeff 4) -
          (3 : F) * f.coeff 3 * d (g.coeff 3) -
          (4 : F) * f.coeff 4 * d (g.coeff 2) -
          (5 : F) * f.coeff 5 * d (g.coeff 1) -
          (6 : F) * f.coeff 6 * d (g.coeff 0) :=
  differentialJacobian_coeff_5_monicOcticDecic d f g hf_high hf8 hf7
    hg_high hg10 hL

set_option maxHeartbeats 64000000 in
/-- The same row integrates: if the degree-`8` and degree-`5` Jacobian
rows vanish, `L` is constant, and the residuals `α, β, γ, δ, ε, ζ, η, θ`
are constant, then the first residual `κ` is a differential constant. -/
theorem scaleZero_muResidual_deriv_zero_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F)
    (L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hepsilon : d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0)
    (hzeta : d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0)
    (heta : d (etaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 V0) = 0)
    (htheta : d (thetaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 W0) = 0)
    (hiota : d (iotaResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 X0) = 0)
    (hrow8 : (9 : F) * L * d G0 + (8 : F) * P * d F0 +
        (7 : F) * Q * d E0 + (6 : F) * R * d D0 +
        (5 : F) * S0 * d C0 + (4 : F) * T0 * d B +
        (3 : F) * U0 * d A -
        F0 * d P - (2 : F) * E0 * d Q -
        (3 : F) * D0 * d R - (4 : F) * C0 * d S0 -
        (5 : F) * B * d T0 - (6 : F) * A * d U0 -
        (8 : F) * d W0 = 0)
    (hrow7 : (8 : F) * P * d G0 + (7 : F) * Q * d F0 +
        (6 : F) * R * d E0 + (5 : F) * S0 * d D0 +
        (4 : F) * T0 * d C0 + (3 : F) * U0 * d B +
        (2 : F) * V0 * d A -
        F0 * d Q - (2 : F) * E0 * d R -
        (3 : F) * D0 * d S0 - (4 : F) * C0 * d T0 -
        (5 : F) * B * d U0 - (6 : F) * A * d V0 -
        (8 : F) * d X0 = 0)
    (hrow : (6 : F) * R * d G0 + (5 : F) * S0 * d F0 +
        (4 : F) * T0 * d E0 + (3 : F) * U0 * d D0 +
        (2 : F) * V0 * d C0 + W0 * d B -
        F0 * d S0 - (2 : F) * E0 * d T0 -
        (3 : F) * D0 * d U0 - (4 : F) * C0 * d V0 -
        (5 : F) * B * d W0 - (6 : F) * A * d X0 = 0) :
    d (muResidual810 L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0) = 0 :=
  muResidual810_deriv_zero d L A B C0 D0 E0 F0 G0 P Q R S0 T0 U0 V0 W0 X0
    hL halpha hbeta hgamma hdelta hepsilon hzeta heta htheta hiota hrow8
    hrow7 hrow

/-! ## Cleared weight-`84` defect on a constant square core -/

set_option maxHeartbeats 64000000 in
/-- On a constant square core the source discriminator is a scalar times
`h⁹`, so the existing ninth-power identities apply with a constant
square root on both the vanishing face `λ = 0` and the nonzero
constant face. -/
theorem scaleZero_eleventhClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda eta : k),
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTwelfthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 84 := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  obtain ⟨lambda, hN⟩ :=
    scaleZero_discriminator_eq_C_mul_ninthPower_810 hp hq hjac ht hH hp8 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_twelfthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨lambda, eta, hN, heta⟩

set_option maxHeartbeats 64000000 in
/-- Aligned constant face `N = 0`: the same degree-`5` clearing applies
with `λ = 0`, and the weight-`84` defect is still a ground constant.
This does not close the face. -/
theorem scaleZero_alignedEleventhClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0) :
    ∃ eta : k,
      localClearedTwelfthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) 0 =
        Polynomial.C eta * (Polynomial.C t) ^ 84 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hN0 :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C (0 : k) * (Polynomial.C t) ^ 9 := by
    simpa [map_zero, zero_mul] using hN
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_twelfthDefectPowerRelation p q H (Polynomial.C t) j 0
      hp hq hh0 hH hp8 hq10 hN0 hD
  exact ⟨eta, heta⟩

set_option maxHeartbeats 64000000 in
/-- Nonzero constant face: `N` is a nonzero scalar times `h⁹`, and the
weight-`84` defect is a ground constant.  This does not close the
face. -/
theorem scaleZero_nonzeroEleventhClearedDefect_exists_C_810
    {p q : k[X][X]} {j t lambda : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (_hlambda : lambda ≠ 0)
    (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
      Polynomial.C lambda * (Polynomial.C t) ^ 9) :
    ∃ eta : k,
      localClearedTwelfthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
          (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 84 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_twelfthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨eta, heta⟩

variable [IsAlgClosed k]

set_option maxHeartbeats 64000000 in
/-- Source-facing tenth residual packet for a normalized scale-zero
`(8,10)` pair: after a square root of the core, the cleared weight-`84`
defect is a ground-field constant. -/
theorem normalized810ScaleZero_exists_eleventhClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
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
        Polynomial.C eta * (Polynomial.C t) ^ 84 := by
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  obtain ⟨t, ht, hHsq⟩ :=
    scaleZero_exists_constantSquareRoot_810 hH hHdegree
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨lambda, eta, hN, hX⟩ :=
    scaleZero_eleventhClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
  exact ⟨t, lambda, eta, ht, hHsq, by simpa only [p, q] using hN,
    by simpa only [p, q] using hX⟩

set_option maxHeartbeats 64000000 in
/-- The weight-`84` defect is a literal ground-field constant. -/
theorem normalized810ScaleZero_eleventhClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
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
        Polynomial.C eta := by
  obtain ⟨t, lambda, eta, ht, hHsq, _hN, hX⟩ :=
    normalized810ScaleZero_exists_eleventhClearedDefect hsource
  refine ⟨t, lambda, eta * t ^ 84, ht, hHsq, ?_⟩
  have hconst :
      localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
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
        Polynomial.C (eta * t ^ 84) := by
    rw [hX, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta (t ^ 84)).symm
  exact hconst

set_option maxHeartbeats 64000000 in
/-- Newton degree of the tenth cleared octic/decic defect at scale
zero. -/
theorem normalized810ScaleZero_eleventhClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
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
  obtain ⟨t, lambda, eta, ht, hHsq, hX⟩ :=
    normalized810ScaleZero_eleventhClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hX]
  exact (natDegree_C eta).le

set_option maxHeartbeats 64000000 in
/-- Aligned/nonzero split of the scale-zero tenth defect: both constant
faces of `N` make the weight-`84` defect a ground constant, and neither
face is excluded or claimed closed. -/
theorem normalized810ScaleZero_eleventhClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let N :=
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
    ∃ t : k, t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
      ((N = 0 ∧
          ∃ eta : k,
            localClearedTwelfthDefect810 (Polynomial.C t) (p.coeff 7)
                (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
                (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
                (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
                (q.coeff 3) (q.coeff 2) (q.coeff 1) 0 =
              Polynomial.C eta * (Polynomial.C t) ^ 84) ∨
        ∃ lambda eta : k, lambda ≠ 0 ∧
          N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
          localClearedTwelfthDefect810 (Polynomial.C t) (p.coeff 7)
              (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
              (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
              (q.coeff 3) (q.coeff 2) (q.coeff 1) lambda =
            Polynomial.C eta * (Polynomial.C t) ^ 84) := by
  dsimp only
  obtain ⟨t, lambda, eta, ht, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_exists_eleventhClearedDefect hsource
  refine ⟨t, ht, hHsq, ?_⟩
  by_cases hlambda : lambda = 0
  · left
    refine ⟨?_, eta, ?_⟩
    · simpa [hlambda, map_zero, zero_mul] using hN
    · simpa [hlambda] using hX
  · exact Or.inr ⟨lambda, eta, hlambda, hN, hX⟩

set_option maxHeartbeats 64000000 in
/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-`84` defect.  Neither vanishing face is claimed closed. -/
theorem normalized810ScaleZero_eleventhClearedDefectBranches
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
      let N :=
        (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
      let X :=
        localClearedTwelfthDefect810 (Polynomial.C t)
          (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1)
          lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      X = Polynomial.C eta ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (eta = 0 ∧ X = 0 ∨
        eta ≠ 0 ∧ X = Polynomial.C eta) := by
  dsimp only
  obtain ⟨t, lambda, eta0, ht, hHsq, hN, hXpow⟩ :=
    normalized810ScaleZero_exists_eleventhClearedDefect hsource
  let eta : k := eta0 * t ^ 84
  have hX :
      localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
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
        Polynomial.C eta := by
    rw [hXpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta0 (t ^ 84)).symm
  refine ⟨t, lambda, eta, ht, hHsq, hN, hX, ?_, ?_⟩
  · by_cases hlambda : lambda = 0
    · left
      refine ⟨hlambda, ?_⟩
      simpa only [hlambda, Polynomial.C_0, zero_mul] using hN
    · right
      refine ⟨hlambda, ?_⟩
      have hNconst :
          (5 : k[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
                  H -
              (4 : k[X]) *
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

set_option maxHeartbeats 64000000 in
/-- Source-facing aligned packet: if the discriminator vanishes, the
weight-`84` defect is still a ground constant.  The face is not
closed. -/
theorem normalized810ScaleZero_aligned_exists_eleventhClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
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
        Polynomial.C eta * (Polynomial.C t) ^ 84 := by
  rcases hsource with
    ⟨hH, hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  obtain ⟨t, ht, hHsq⟩ :=
    scaleZero_exists_constantSquareRoot_810 hH hHdegree
  let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  obtain ⟨eta, hX⟩ :=
    scaleZero_alignedEleventhClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hNzero)
  exact ⟨t, eta, ht, hHsq, by simpa only [p, q] using hX⟩

set_option maxHeartbeats 64000000 in
/-- Source-facing nonzero packet: if the discriminator is a nonzero
ground constant, the weight-`84` defect is still a ground constant.
The face is not closed. -/
theorem normalized810ScaleZero_nonzero_exists_eleventhClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedTwelfthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
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
        Polynomial.C eta * (Polynomial.C t) ^ 84 := by
  obtain ⟨t, lambda, eta, ht, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_exists_eleventhClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro h0
    apply hNnonzero
    simpa [h0, map_zero, zero_mul] using hN
  exact ⟨t, lambda, eta, ht, hlambda, hHsq, hN, hX⟩

end ScaleZeroEleventhDefect810


#print axioms fableScaleZero_twelfthCoefficientJacobianRow_raw_810
#print axioms scaleZero_twelfthCoefficientJacobianRow_810
#print axioms normalized810ScaleZero_twelfthCoefficientJacobianRow
#print axioms normalized810ScaleZero_twelfthCoefficientJacobianRow_collapsed
#print axioms differentialJacobian_coeff_5_monicOcticDecic
#print axioms scaleZero_monicOcticDecic_degree5Row_810
#print axioms muResidual810_deriv_zero
#print axioms scaleZero_muResidual_deriv_zero_810
#print axioms affineDepress_degreeTen_coeff1_810
#print axioms twelfthDefect_eq_clearedMu810
#print axioms nonzeroFace810_twelfthDefectPowerRelation
#print axioms scaleZero_eleventhClearedDefect_exists_C_810
#print axioms scaleZero_alignedEleventhClearedDefect_exists_C_810
#print axioms scaleZero_nonzeroEleventhClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_eleventhClearedDefect
#print axioms normalized810ScaleZero_eleventhClearedDefect_exists_C
#print axioms normalized810ScaleZero_eleventhClearedDefect_natDegree_le_zero
#print axioms normalized810ScaleZero_eleventhClearedDefectFirstFace
#print axioms normalized810ScaleZero_eleventhClearedDefectBranches
#print axioms normalized810ScaleZero_aligned_exists_eleventhClearedDefect
#print axioms normalized810ScaleZero_nonzero_exists_eleventhClearedDefect

end Max11DegreeRoutes
end
