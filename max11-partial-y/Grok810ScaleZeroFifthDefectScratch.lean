import LowScale810ScaleZeroFourthDefect
import LowScale810ScaleTwoSixthFace

/-! # Scale-zero fifth defect for the normalized `(8,10)`, `H = 0` leaf

The fourth-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first four octic/decic defects to ground constants times `h¹⁴`, `h²¹`,
`h²⁸`, and `h³⁵`.  This file consumes the next unused Keller coefficient
of the same monic octic-decic depression: the degree-`11` Jacobian row is
`10 E' + 9 L D' + 8 P C' + 7 Q B' + 6 R A' - 4 C P' - 5 B Q' - 6 A R' - 8 T' = 0`.
The corresponding sixth cleared polynomial defect of weight forty-two is
likewise a ground-field constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  Root-evaluation from the scale-two
sixth face is unavailable, because a nonzero constant has no finite
root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`10` residual of
the same monic depression.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ScaleZeroFifthDefect810

variable {k : Type*} [Field k] [CharZero k]

/-! ## Degree-`11` source Jacobian row -/

/-- Source-facing degree-`11` Jacobian row of a normalized scale-zero
`(8,10)` pair. -/
theorem normalized810ScaleZero_sixthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 8).derivative * (q.coeff 4 * Polynomial.C (4 : k)) +
        (p.coeff 7).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 6).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 5).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 3).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 2).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 8 * Polynomial.C (8 : k)) * (q.coeff 4).derivative +
        (p.coeff 7 * Polynomial.C (7 : k)) * (q.coeff 5).derivative +
        (p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 6).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 7).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 8).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 9).derivative +
        (p.coeff 2 * Polynomial.C (2 : k)) * (q.coeff 10).derivative) =
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
  simpa only [p, q] using sixthCoefficientJacobianRow_810 hp hq hjac

/-- At scale zero the common core is constant, so the leading octic and
decic coefficients of the degree-`11` row are differential constants. -/
theorem scaleZero_sixthCoefficientJacobianRow_810
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 7).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 6).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 5).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 3).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 2).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 8 * Polynomial.C (8 : k)) * (q.coeff 4).derivative +
        (p.coeff 7 * Polynomial.C (7 : k)) * (q.coeff 5).derivative +
        (p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 6).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 7).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 8).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 9).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp8der : (p.coeff 8).derivative = 0 := by
    rw [hp8, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := sixthCoefficientJacobianRow_810 hp hq hjac
  simpa [hp8der, hq10der] using hrow

/-- Source-facing scale-zero collapse of the degree-`11` row. -/
theorem normalized810ScaleZero_sixthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 7).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 6).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 5).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 4).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 3).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 2).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 8 * Polynomial.C (8 : k)) * (q.coeff 4).derivative +
        (p.coeff 7 * Polynomial.C (7 : k)) * (q.coeff 5).derivative +
        (p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 6).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 7).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 8).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 9).derivative) =
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
    scaleZero_sixthCoefficientJacobianRow_810 hp hq hjac hHdegree
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)

/-! ## Degree-`11` monic Jacobian row -/

/-- For a monic octic and a monic decic whose `z⁹` coefficient `L` is
already a differential constant, the degree-`11` Jacobian coefficient
is exactly
`10 E' + 9 L D' + 8 P C' + 7 Q B' + 6 R A' - 4 C P' - 5 B Q' - 6 A R' - 8 T'`.
Here `A = f.coeff 6`, `B = f.coeff 5`, `C = f.coeff 4`, `D = f.coeff 3`,
`E = f.coeff 2`, `L = g.coeff 9`, `P = g.coeff 8`, `Q = g.coeff 7`,
`R = g.coeff 6`, and `T = g.coeff 4`. -/
theorem scaleZero_monicOcticDecic_degree11Row_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 11 =
      (10 : F) * d (f.coeff 2) + (9 : F) * g.coeff 9 * d (f.coeff 3) +
        (8 : F) * g.coeff 8 * d (f.coeff 4) +
        (7 : F) * g.coeff 7 * d (f.coeff 5) +
        (6 : F) * g.coeff 6 * d (f.coeff 6) -
          (4 : F) * f.coeff 4 * d (g.coeff 8) -
          (5 : F) * f.coeff 5 * d (g.coeff 7) -
          (6 : F) * f.coeff 6 * d (g.coeff 6) -
          (8 : F) * d (g.coeff 4) :=
  differentialJacobian_coeff_11_monicOcticDecic d f g hf_high hf8 hf7
    hg_high hg10 hL

/-- The same row integrates: if
`10 E' + 9 L D' + 8 P C' + 7 Q B' + 6 R A' - 4 C P' - 5 B Q' - 6 A R' - 8 T' = 0`,
`L` is constant, the second-face residual `P - (5/4) A` is constant,
the third-face residual `Q - (5/4) B - (9/8) L A` is constant,
and the fourth-face residual
`R - (5/4) C - (5/32) A² - (9/8) L B - α A` is constant, then the first
residual
`T - (5/4) E - (5/32) B² - (5/16) A C + (5/128) A³
  - L ((9/8) D + (9/64) A B) - α C - (7/8) β B - (3/4) γ A`
is a differential constant. -/
theorem scaleZero_epsilonResidual_deriv_zero_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (L A B C0 D0 E0 P Q R T0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hgamma : d (gammaResidual810 L A B C0 P R) = 0)
    (hrow : (10 : F) * d E0 + (9 : F) * L * d D0 +
        (8 : F) * P * d C0 + (7 : F) * Q * d B +
        (6 : F) * R * d A - (4 : F) * C0 * d P -
        (5 : F) * B * d Q - (6 : F) * A * d R -
        (8 : F) * d T0 = 0) :
    d (epsilonResidual810 L A B C0 D0 E0 P Q R T0) = 0 :=
  epsilonResidual810_deriv_zero d L A B C0 D0 E0 P Q R T0 hL halpha
    hbeta hgamma hrow

/-! ## Cleared weight-`42` defect on a constant square core -/

/-- On a constant square core the source discriminator is a scalar times
`h⁹`, so the existing ninth-power identities apply with a constant
square root on both the vanishing face `λ = 0` and the nonzero
constant face. -/
theorem scaleZero_fifthClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda zeta : k),
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedSixthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
        Polynomial.C zeta * (Polynomial.C t) ^ 42 := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  obtain ⟨lambda, hN⟩ :=
    scaleZero_discriminator_eq_C_mul_ninthPower_810 hp hq hjac ht hH hp8 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨zeta, hzeta⟩ :=
    nonzeroFace810_sixthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨lambda, zeta, hN, hzeta⟩

/-- Aligned constant face `N = 0`: the same degree-`11` clearing applies
with `λ = 0`, and the weight-`42` defect is still a ground constant.
This does not close the face. -/
theorem scaleZero_alignedFifthClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0) :
    ∃ zeta : k,
      localClearedSixthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) 0 =
        Polynomial.C zeta * (Polynomial.C t) ^ 42 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hN0 :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C (0 : k) * (Polynomial.C t) ^ 9 := by
    simpa [map_zero, zero_mul] using hN
  obtain ⟨zeta, hzeta⟩ :=
    nonzeroFace810_sixthDefectPowerRelation p q H (Polynomial.C t) j 0
      hp hq hh0 hH hp8 hq10 hN0 hD
  exact ⟨zeta, hzeta⟩

/-- Nonzero constant face: `N` is a nonzero scalar times `h⁹`, and the
weight-`42` defect is a ground constant.  This does not close the
face. -/
theorem scaleZero_nonzeroFifthClearedDefect_exists_C_810
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
    ∃ zeta : k,
      localClearedSixthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) lambda =
        Polynomial.C zeta * (Polynomial.C t) ^ 42 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨zeta, hzeta⟩ :=
    nonzeroFace810_sixthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨zeta, hzeta⟩

variable [IsAlgClosed k]

/-- Source-facing fifth residual packet for a normalized scale-zero
`(8,10)` pair: after a square root of the core, the cleared weight-`42`
defect is a ground-field constant. -/
theorem normalized810ScaleZero_exists_fifthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda zeta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedSixthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          lambda =
        Polynomial.C zeta * (Polynomial.C t) ^ 42 := by
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
  obtain ⟨lambda, zeta, hN, hW⟩ :=
    scaleZero_fifthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
  exact ⟨t, lambda, zeta, ht, hHsq, by simpa only [p, q] using hN,
    by simpa only [p, q] using hW⟩

/-- Newton degree of the sixth cleared octic/decic defect at scale
zero. -/
theorem normalized810ScaleZero_fifthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedSixthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, zeta, ht, hHsq, _hN, hW⟩ :=
    normalized810ScaleZero_exists_fifthClearedDefect hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  have hconst :
      localClearedSixthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          lambda =
        Polynomial.C (zeta * t ^ 42) := by
    rw [hW, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) zeta (t ^ 42)).symm
  rw [hconst]
  exact (natDegree_C (zeta * t ^ 42)).le

/-- Aligned/nonzero split of the scale-zero fifth defect: both constant
faces of `N` make the weight-`42` defect a ground constant, and neither
face is excluded or claimed closed. -/
theorem normalized810ScaleZero_fifthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let N :=
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
    ∃ t : k, t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
      ((N = 0 ∧
          ∃ zeta : k,
            localClearedSixthDefect810 (Polynomial.C t) (p.coeff 7)
                (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
                (p.coeff 2) (q.coeff 8) (q.coeff 7) (q.coeff 6)
                (q.coeff 5) (q.coeff 4) 0 =
              Polynomial.C zeta * (Polynomial.C t) ^ 42) ∨
        ∃ lambda zeta : k, lambda ≠ 0 ∧
          N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
          localClearedSixthDefect810 (Polynomial.C t) (p.coeff 7)
              (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (p.coeff 2) (q.coeff 8) (q.coeff 7) (q.coeff 6)
              (q.coeff 5) (q.coeff 4) lambda =
            Polynomial.C zeta * (Polynomial.C t) ^ 42) := by
  dsimp only
  obtain ⟨t, lambda, zeta, ht, hHsq, hN, hW⟩ :=
    normalized810ScaleZero_exists_fifthClearedDefect hsource
  refine ⟨t, ht, hHsq, ?_⟩
  by_cases hlambda : lambda = 0
  · left
    refine ⟨?_, zeta, ?_⟩
    · simpa [hlambda, map_zero, zero_mul] using hN
    · simpa [hlambda] using hW
  · exact Or.inr ⟨lambda, zeta, hlambda, hN, hW⟩

/-- Source-facing aligned packet: if the discriminator vanishes, the
weight-`42` defect is still a ground constant.  The face is not
closed. -/
theorem normalized810ScaleZero_aligned_exists_fifthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t zeta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedSixthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          0 =
        Polynomial.C zeta * (Polynomial.C t) ^ 42 := by
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
  obtain ⟨zeta, hW⟩ :=
    scaleZero_alignedFifthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hNzero)
  exact ⟨t, zeta, ht, hHsq, by simpa only [p, q] using hW⟩

/-- Source-facing nonzero packet: if the discriminator is a nonzero
ground constant, the weight-`42` defect is still a ground constant.
The face is not closed. -/
theorem normalized810ScaleZero_nonzero_exists_fifthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda zeta : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedSixthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 2)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 4)
          lambda =
        Polynomial.C zeta * (Polynomial.C t) ^ 42 := by
  obtain ⟨t, lambda, zeta, ht, hHsq, hN, hW⟩ :=
    normalized810ScaleZero_exists_fifthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro h0
    apply hNnonzero
    simpa [h0, map_zero, zero_mul] using hN
  exact ⟨t, lambda, zeta, ht, hlambda, hHsq, hN, hW⟩

end ScaleZeroFifthDefect810

#print axioms normalized810ScaleZero_sixthCoefficientJacobianRow
#print axioms scaleZero_sixthCoefficientJacobianRow_810
#print axioms normalized810ScaleZero_sixthCoefficientJacobianRow_collapsed
#print axioms scaleZero_monicOcticDecic_degree11Row_810
#print axioms scaleZero_epsilonResidual_deriv_zero_810
#print axioms scaleZero_fifthClearedDefect_exists_C_810
#print axioms scaleZero_alignedFifthClearedDefect_exists_C_810
#print axioms scaleZero_nonzeroFifthClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_fifthClearedDefect
#print axioms normalized810ScaleZero_fifthClearedDefect_natDegree_le_zero
#print axioms normalized810ScaleZero_fifthClearedDefectFirstFace
#print axioms normalized810ScaleZero_aligned_exists_fifthClearedDefect
#print axioms normalized810ScaleZero_nonzero_exists_fifthClearedDefect

end Max11DegreeRoutes
