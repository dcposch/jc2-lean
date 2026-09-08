import Grok810ScaleZeroFifthDefectScratch
import LowScale810ScaleTwoSeventhFace

/-! # Scale-zero sixth defect for the normalized `(8,10)`, `H = 0` leaf

The fifth-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first five octic/decic defects to ground constants times `h¹⁴`, `h²¹`,
`h²⁸`, `h³⁵`, and `h⁴²`.  This file consumes the next unused Keller
coefficient of the same monic octic-decic depression: the degree-`10`
Jacobian row is
`10 F' + 9 L E' + 8 P D' + 7 Q C' + 6 R B' + 5 S A' - 3 D P' - 4 C Q'
- 5 B R' - 6 A S' - 8 U' = 0`.  The corresponding seventh cleared
polynomial defect of weight forty-nine is likewise a ground-field
constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  The same zero/nonzero split is recorded
for the weight-`49` defect itself.  Root-evaluation from the scale-two
seventh face is unavailable, because a nonzero constant has no finite
root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`9` residual of
the same monic depression.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ScaleZeroSixthDefect810

variable {k : Type*} [Field k] [CharZero k]

/-! ## Degree-`10` source Jacobian row -/

/-- Source-facing degree-`10` Jacobian row of a normalized scale-zero
`(8,10)` pair. -/
theorem normalized810ScaleZero_seventhCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 8).derivative * (q.coeff 3 * Polynomial.C (3 : k)) +
        (p.coeff 7).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 6).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 5).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 2).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 1).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 8 * Polynomial.C (8 : k)) * (q.coeff 3).derivative +
        (p.coeff 7 * Polynomial.C (7 : k)) * (q.coeff 4).derivative +
        (p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 5).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 6).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 7).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 8).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 9).derivative +
        (p.coeff 1 * Polynomial.C (1 : k)) * (q.coeff 10).derivative) =
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
  simpa only [p, q] using seventhCoefficientJacobianRow_810 hp hq hjac

/-- At scale zero the common core is constant, so the leading octic and
decic coefficients of the degree-`10` row are differential constants. -/
theorem scaleZero_seventhCoefficientJacobianRow_810
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 7).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 6).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 5).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 2).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 1).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 8 * Polynomial.C (8 : k)) * (q.coeff 3).derivative +
        (p.coeff 7 * Polynomial.C (7 : k)) * (q.coeff 4).derivative +
        (p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 5).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 6).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 7).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 8).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 9).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp8der : (p.coeff 8).derivative = 0 := by
    rw [hp8, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := seventhCoefficientJacobianRow_810 hp hq hjac
  simpa [hp8der, hq10der] using hrow

/-- Source-facing scale-zero collapse of the degree-`10` row. -/
theorem normalized810ScaleZero_seventhCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 7).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 6).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 5).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 4).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 3).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 2).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 1).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 8 * Polynomial.C (8 : k)) * (q.coeff 3).derivative +
        (p.coeff 7 * Polynomial.C (7 : k)) * (q.coeff 4).derivative +
        (p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 5).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 6).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 7).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 8).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 9).derivative) =
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
    scaleZero_seventhCoefficientJacobianRow_810 hp hq hjac hHdegree
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)

/-! ## Degree-`10` monic Jacobian row -/

/-- For a monic octic and a monic decic whose `z⁹` coefficient `L` is
already a differential constant, the degree-`10` Jacobian coefficient
is exactly
`10 F' + 9 L E' + 8 P D' + 7 Q C' + 6 R B' + 5 S A' - 3 D P' - 4 C Q'
- 5 B R' - 6 A S' - 8 U'`.
Here `A = f.coeff 6`, `B = f.coeff 5`, `C = f.coeff 4`, `D = f.coeff 3`,
`E = f.coeff 2`, `F = f.coeff 1`, `L = g.coeff 9`, `P = g.coeff 8`,
`Q = g.coeff 7`, `R = g.coeff 6`, `S = g.coeff 5`, and `U = g.coeff 3`. -/
theorem scaleZero_monicOcticDecic_degree10Row_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 10 =
      (10 : F) * d (f.coeff 1) + (9 : F) * g.coeff 9 * d (f.coeff 2) +
        (8 : F) * g.coeff 8 * d (f.coeff 3) +
        (7 : F) * g.coeff 7 * d (f.coeff 4) +
        (6 : F) * g.coeff 6 * d (f.coeff 5) +
        (5 : F) * g.coeff 5 * d (f.coeff 6) -
          (3 : F) * f.coeff 3 * d (g.coeff 8) -
          (4 : F) * f.coeff 4 * d (g.coeff 7) -
          (5 : F) * f.coeff 5 * d (g.coeff 6) -
          (6 : F) * f.coeff 6 * d (g.coeff 5) -
          (8 : F) * d (g.coeff 3) :=
  differentialJacobian_coeff_10_monicOcticDecic d f g hf_high hf8 hf7
    hg_high hg10 hL

/-- The same row integrates: if
`10 F' + 9 L E' + 8 P D' + 7 Q C' + 6 R B' + 5 S A' - 3 D P' - 4 C Q'
- 5 B R' - 6 A S' - 8 U' = 0`,
`L` is constant, the second-face residual `P - (5/4) A` is constant,
the third-face residual `Q - (5/4) B - (9/8) L A` is constant,
the fourth-face residual
`R - (5/4) C - (5/32) A² - (9/8) L B - α A` is constant,
and the fifth-face residual
`S - (5/4) D - (9/8) L C - α B - (7/8) β A - (5/16) A B - (9/128) L A²`
is constant, then the first residual
`U - (5/4) F - (9/8) L E - α D - (7/8) β C - (3/4) γ B - (5/8) δ A
- (5/16) A D - (5/16) B C + (7/128) β A² + (15/128) A² B
+ (21/1024) L A³ - (9/64) L A C - (9/128) L B²`
is a differential constant. -/
theorem scaleZero_zetaResidual_deriv_zero_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (L A B C0 D0 E0 F0 P Q R S0 U0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hdelta : d (deltaResidual810 L A B C0 D0 P Q S0) = 0)
    (hrow : (10 : F) * d F0 + (9 : F) * L * d E0 +
        (8 : F) * P * d D0 + (7 : F) * Q * d C0 +
        (6 : F) * R * d B + (5 : F) * S0 * d A -
        (3 : F) * D0 * d P - (4 : F) * C0 * d Q -
        (5 : F) * B * d R - (6 : F) * A * d S0 -
        (8 : F) * d U0 = 0) :
    d (zetaResidual810 L A B C0 D0 E0 F0 P Q R S0 U0) = 0 :=
  zetaResidual810_deriv_zero d L A B C0 D0 E0 F0 P Q R S0 U0 hL halpha
    hbeta hgamma hdelta hrow

/-! ## Cleared weight-`49` defect on a constant square core -/

/-- On a constant square core the source discriminator is a scalar times
`h⁹`, so the existing ninth-power identities apply with a constant
square root on both the vanishing face `λ = 0` and the nonzero
constant face. -/
theorem scaleZero_sixthClearedDefect_exists_C_810
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
      localClearedSeventhDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 49 := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  obtain ⟨lambda, hN⟩ :=
    scaleZero_discriminator_eq_C_mul_ninthPower_810 hp hq hjac ht hH hp8 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_seventhDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨lambda, eta, hN, heta⟩

/-- Aligned constant face `N = 0`: the same degree-`10` clearing applies
with `λ = 0`, and the weight-`49` defect is still a ground constant.
This does not close the face. -/
theorem scaleZero_alignedSixthClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0) :
    ∃ eta : k,
      localClearedSeventhDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) 0 =
        Polynomial.C eta * (Polynomial.C t) ^ 49 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hN0 :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C (0 : k) * (Polynomial.C t) ^ 9 := by
    simpa [map_zero, zero_mul] using hN
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_seventhDefectPowerRelation p q H (Polynomial.C t) j 0
      hp hq hh0 hH hp8 hq10 hN0 hD
  exact ⟨eta, heta⟩

/-- Nonzero constant face: `N` is a nonzero scalar times `h⁹`, and the
weight-`49` defect is a ground constant.  This does not close the
face. -/
theorem scaleZero_nonzeroSixthClearedDefect_exists_C_810
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
      localClearedSeventhDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
          (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4)
          (q.coeff 3) lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 49 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eta, heta⟩ :=
    nonzeroFace810_seventhDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨eta, heta⟩

variable [IsAlgClosed k]

/-- Source-facing sixth residual packet for a normalized scale-zero
`(8,10)` pair: after a square root of the core, the cleared weight-`49`
defect is a ground-field constant. -/
theorem normalized810ScaleZero_exists_sixthClearedDefect
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
      localClearedSeventhDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 49 := by
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
    scaleZero_sixthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
  exact ⟨t, lambda, eta, ht, hHsq, by simpa only [p, q] using hN,
    by simpa only [p, q] using hX⟩

/-- The weight-`49` defect is a literal ground-field constant. -/
theorem normalized810ScaleZero_sixthClearedDefect_exists_C
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedSeventhDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          lambda =
        Polynomial.C eta := by
  obtain ⟨t, lambda, eta, ht, hHsq, _hN, hX⟩ :=
    normalized810ScaleZero_exists_sixthClearedDefect hsource
  refine ⟨t, lambda, eta * t ^ 49, ht, hHsq, ?_⟩
  have hconst :
      localClearedSeventhDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          lambda =
        Polynomial.C (eta * t ^ 49) := by
    rw [hX, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta (t ^ 49)).symm
  exact hconst

/-- Newton degree of the seventh cleared octic/decic defect at scale
zero. -/
theorem normalized810ScaleZero_sixthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedSeventhDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, eta, ht, hHsq, hX⟩ :=
    normalized810ScaleZero_sixthClearedDefect_exists_C hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  rw [hX]
  exact (natDegree_C eta).le

/-- Aligned/nonzero split of the scale-zero sixth defect: both constant
faces of `N` make the weight-`49` defect a ground constant, and neither
face is excluded or claimed closed. -/
theorem normalized810ScaleZero_sixthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let N :=
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
    ∃ t : k, t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
      ((N = 0 ∧
          ∃ eta : k,
            localClearedSeventhDefect810 (Polynomial.C t) (p.coeff 7)
                (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
                (p.coeff 2) (p.coeff 1) (q.coeff 8) (q.coeff 7)
                (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) 0 =
              Polynomial.C eta * (Polynomial.C t) ^ 49) ∨
        ∃ lambda eta : k, lambda ≠ 0 ∧
          N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
          localClearedSeventhDefect810 (Polynomial.C t) (p.coeff 7)
              (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (p.coeff 1) (q.coeff 8) (q.coeff 7)
              (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda =
            Polynomial.C eta * (Polynomial.C t) ^ 49) := by
  dsimp only
  obtain ⟨t, lambda, eta, ht, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_exists_sixthClearedDefect hsource
  refine ⟨t, ht, hHsq, ?_⟩
  by_cases hlambda : lambda = 0
  · left
    refine ⟨?_, eta, ?_⟩
    · simpa [hlambda, map_zero, zero_mul] using hN
    · simpa [hlambda] using hX
  · exact Or.inr ⟨lambda, eta, hlambda, hN, hX⟩

/-- Explicit zero/nonzero constant branches of both the discriminator and
the weight-`49` defect.  Neither vanishing face is claimed closed. -/
theorem normalized810ScaleZero_sixthClearedDefectBranches
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
        localClearedSeventhDefect810 (Polynomial.C t)
          (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          (q.coeff 5) (q.coeff 4) (q.coeff 3) lambda
      N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      X = Polynomial.C eta ∧
      (lambda = 0 ∧ N = 0 ∨
        lambda ≠ 0 ∧ N = Polynomial.C (lambda * t ^ 9)) ∧
      (eta = 0 ∧ X = 0 ∨
        eta ≠ 0 ∧ X = Polynomial.C eta) := by
  dsimp only
  obtain ⟨t, lambda, eta0, ht, hHsq, hN, hXpow⟩ :=
    normalized810ScaleZero_exists_sixthClearedDefect hsource
  let eta : k := eta0 * t ^ 49
  have hX :
      localClearedSeventhDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          lambda =
        Polynomial.C eta := by
    rw [hXpow, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eta0 (t ^ 49)).symm
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

/-- Source-facing aligned packet: if the discriminator vanishes, the
weight-`49` defect is still a ground constant.  The face is not
closed. -/
theorem normalized810ScaleZero_aligned_exists_sixthClearedDefect
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
      localClearedSeventhDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          0 =
        Polynomial.C eta * (Polynomial.C t) ^ 49 := by
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
    scaleZero_alignedSixthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hNzero)
  exact ⟨t, eta, ht, hHsq, by simpa only [p, q] using hX⟩

/-- Source-facing nonzero packet: if the discriminator is a nonzero
ground constant, the weight-`49` defect is still a ground constant.
The face is not closed. -/
theorem normalized810ScaleZero_nonzero_exists_sixthClearedDefect
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
      localClearedSeventhDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 1)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 3)
          lambda =
        Polynomial.C eta * (Polynomial.C t) ^ 49 := by
  obtain ⟨t, lambda, eta, ht, hHsq, hN, hX⟩ :=
    normalized810ScaleZero_exists_sixthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro h0
    apply hNnonzero
    simpa [h0, map_zero, zero_mul] using hN
  exact ⟨t, lambda, eta, ht, hlambda, hHsq, hN, hX⟩

end ScaleZeroSixthDefect810

#print axioms normalized810ScaleZero_seventhCoefficientJacobianRow
#print axioms scaleZero_seventhCoefficientJacobianRow_810
#print axioms normalized810ScaleZero_seventhCoefficientJacobianRow_collapsed
#print axioms scaleZero_monicOcticDecic_degree10Row_810
#print axioms scaleZero_zetaResidual_deriv_zero_810
#print axioms scaleZero_sixthClearedDefect_exists_C_810
#print axioms scaleZero_alignedSixthClearedDefect_exists_C_810
#print axioms scaleZero_nonzeroSixthClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_sixthClearedDefect
#print axioms normalized810ScaleZero_sixthClearedDefect_exists_C
#print axioms normalized810ScaleZero_sixthClearedDefect_natDegree_le_zero
#print axioms normalized810ScaleZero_sixthClearedDefectFirstFace
#print axioms normalized810ScaleZero_sixthClearedDefectBranches
#print axioms normalized810ScaleZero_aligned_exists_sixthClearedDefect
#print axioms normalized810ScaleZero_nonzero_exists_sixthClearedDefect

end Max11DegreeRoutes
