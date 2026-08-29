import LowScale810ScaleZeroThirdDefect
import LowScale810ScaleTwoFifthFace

/-! # Scale-zero fourth defect for the normalized `(8,10)`, `H = 0` leaf

The third-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first three octic/decic defects to ground constants times `h¹⁴`, `h²¹`,
and `h²⁸`.  This file consumes the next unused Keller coefficient of the
same monic octic-decic depression: the degree-`12` Jacobian row is
`10 D' + 9 L C' + 8 P B' + 7 Q A' - 5 B P' - 6 A Q' - 8 S' = 0`.  The
corresponding fifth cleared polynomial defect of weight thirty-five is
likewise a ground-field constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  Root-evaluation from the scale-two
fifth face is unavailable, because a nonzero constant has no finite
root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`11` residual of
the same monic depression.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ScaleZeroFourthDefect810

variable {k : Type*} [Field k] [CharZero k]

/-! ## Degree-`12` source Jacobian row -/

/-- Source-facing degree-`12` Jacobian row of a normalized scale-zero
`(8,10)` pair. -/
theorem normalized810ScaleZero_fifthCoefficientJacobianRow
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 8).derivative * (q.coeff 5 * Polynomial.C (5 : k)) +
        (p.coeff 7).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 6).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 5).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 4).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 3).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 8 * Polynomial.C (8 : k)) * (q.coeff 5).derivative +
        (p.coeff 7 * Polynomial.C (7 : k)) * (q.coeff 6).derivative +
        (p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 7).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 8).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 9).derivative +
        (p.coeff 3 * Polynomial.C (3 : k)) * (q.coeff 10).derivative) =
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
  simpa only [p, q] using fifthCoefficientJacobianRow_810 hp hq hjac

/-- At scale zero the common core is constant, so the leading octic and
decic coefficients of the degree-`12` row are differential constants. -/
theorem scaleZero_fifthCoefficientJacobianRow_810
    {p q : k[X][X]} {j : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j))
    (hHdegree : H.natDegree = 0)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    (p.coeff 7).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 6).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 5).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 4).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 3).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 8 * Polynomial.C (8 : k)) * (q.coeff 5).derivative +
        (p.coeff 7 * Polynomial.C (7 : k)) * (q.coeff 6).derivative +
        (p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 7).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 8).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 9).derivative) =
      0 := by
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hHdegree
  have hHder : H.derivative = 0 := by
    rw [← hc, derivative_C]
  have hp8der : (p.coeff 8).derivative = 0 := by
    rw [hp8, derivative_pow, hHder, mul_zero]
  have hq10der : (q.coeff 10).derivative = 0 := by
    rw [hq10, derivative_pow, hHder, mul_zero]
  have hrow := fifthCoefficientJacobianRow_810 hp hq hjac
  simpa [hp8der, hq10der] using hrow

/-- Source-facing scale-zero collapse of the degree-`12` row. -/
theorem normalized810ScaleZero_fifthCoefficientJacobianRow_collapsed
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    (p.coeff 7).derivative * (q.coeff 6 * Polynomial.C (6 : k)) +
        (p.coeff 6).derivative * (q.coeff 7 * Polynomial.C (7 : k)) +
        (p.coeff 5).derivative * (q.coeff 8 * Polynomial.C (8 : k)) +
        (p.coeff 4).derivative * (q.coeff 9 * Polynomial.C (9 : k)) +
        (p.coeff 3).derivative * (q.coeff 10 * Polynomial.C (10 : k)) -
      ((p.coeff 8 * Polynomial.C (8 : k)) * (q.coeff 5).derivative +
        (p.coeff 7 * Polynomial.C (7 : k)) * (q.coeff 6).derivative +
        (p.coeff 6 * Polynomial.C (6 : k)) * (q.coeff 7).derivative +
        (p.coeff 5 * Polynomial.C (5 : k)) * (q.coeff 8).derivative +
        (p.coeff 4 * Polynomial.C (4 : k)) * (q.coeff 9).derivative) =
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
    scaleZero_fifthCoefficientJacobianRow_810 hp hq hjac hHdegree
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)

/-! ## Degree-`12` monic Jacobian row -/

/-- For a monic octic and a monic decic whose `z⁹` coefficient `L` is
already a differential constant, the degree-`12` Jacobian coefficient
is exactly `10 D' + 9 L C' + 8 P B' + 7 Q A' - 5 B P' - 6 A Q' - 8 S'`.
Here `A = f.coeff 6`, `B = f.coeff 5`, `C = f.coeff 4`, `D = f.coeff 3`,
`L = g.coeff 9`, `P = g.coeff 8`, `Q = g.coeff 7`, and `S = g.coeff 5`. -/
theorem scaleZero_monicOcticDecic_degree12Row_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 12 =
      (10 : F) * d (f.coeff 3) + (9 : F) * g.coeff 9 * d (f.coeff 4) +
        (8 : F) * g.coeff 8 * d (f.coeff 5) +
        (7 : F) * g.coeff 7 * d (f.coeff 6) -
          (5 : F) * f.coeff 5 * d (g.coeff 8) -
          (6 : F) * f.coeff 6 * d (g.coeff 7) -
          (8 : F) * d (g.coeff 5) :=
  differentialJacobian_coeff_12_monicOcticDecic d f g hf_high hf8 hf7
    hg_high hg10 hL

/-- The same row integrates: if
`10 D' + 9 L C' + 8 P B' + 7 Q A' - 5 B P' - 6 A Q' - 8 S' = 0`,
`L` is constant, the second-face residual `P - (5/4) A` is constant,
and the third-face residual `Q - (5/4) B - (9/8) L A` is constant,
then the first residual
`S - (5/4) D - (9/8) L C - α B - (7/8) β A - (5/16) A B - (9/128) L A²`
is a differential constant. -/
theorem scaleZero_deltaResidual_deriv_zero_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (L A B C0 D0 P Q S0 : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hbeta : d (betaResidual810 L A B Q) = 0)
    (hrow : (10 : F) * d D0 + (9 : F) * L * d C0 +
        (8 : F) * P * d B + (7 : F) * Q * d A -
        (5 : F) * B * d P - (6 : F) * A * d Q -
        (8 : F) * d S0 = 0) :
    d (deltaResidual810 L A B C0 D0 P Q S0) = 0 :=
  deltaResidual810_deriv_zero d L A B C0 D0 P Q S0 hL halpha hbeta hrow

/-! ## Cleared weight-`35` defect on a constant square core -/

/-- On a constant square core the source discriminator is a scalar times
`h⁹`, so the existing ninth-power identities apply with a constant
square root on both the vanishing face `λ = 0` and the nonzero
constant face. -/
theorem scaleZero_fourthClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda eps : k),
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedFifthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) lambda =
        Polynomial.C eps * (Polynomial.C t) ^ 35 := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  obtain ⟨lambda, hN⟩ :=
    scaleZero_discriminator_eq_C_mul_ninthPower_810 hp hq hjac ht hH hp8 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eps, heps⟩ :=
    nonzeroFace810_fifthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨lambda, eps, hN, heps⟩

/-- Aligned constant face `N = 0`: the same degree-`12` clearing applies
with `λ = 0`, and the weight-`35` defect is still a ground constant.
This does not close the face. -/
theorem scaleZero_alignedFourthClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0) :
    ∃ eps : k,
      localClearedFifthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) 0 =
        Polynomial.C eps * (Polynomial.C t) ^ 35 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hN0 :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C (0 : k) * (Polynomial.C t) ^ 9 := by
    simpa [map_zero, zero_mul] using hN
  obtain ⟨eps, heps⟩ :=
    nonzeroFace810_fifthDefectPowerRelation p q H (Polynomial.C t) j 0
      hp hq hh0 hH hp8 hq10 hN0 hD
  exact ⟨eps, heps⟩

/-- Nonzero constant face: `N` is a nonzero scalar times `h⁹`, and the
weight-`35` defect is a ground constant.  This does not close the
face. -/
theorem scaleZero_nonzeroFourthClearedDefect_exists_C_810
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
    ∃ eps : k,
      localClearedFifthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (p.coeff 3) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) lambda =
        Polynomial.C eps * (Polynomial.C t) ^ 35 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨eps, heps⟩ :=
    nonzeroFace810_fifthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨eps, heps⟩

variable [IsAlgClosed k]

/-- Source-facing fourth residual packet for a normalized scale-zero
`(8,10)` pair: after a square root of the core, the cleared weight-`35`
defect is a ground-field constant. -/
theorem normalized810ScaleZero_exists_fourthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda eps : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedFifthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          lambda =
        Polynomial.C eps * (Polynomial.C t) ^ 35 := by
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
  obtain ⟨lambda, eps, hN, hV⟩ :=
    scaleZero_fourthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
  exact ⟨t, lambda, eps, ht, hHsq, by simpa only [p, q] using hN,
    by simpa only [p, q] using hV⟩

/-- Newton degree of the fifth cleared octic/decic defect at scale
zero. -/
theorem normalized810ScaleZero_fourthClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedFifthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, eps, ht, hHsq, _hN, hV⟩ :=
    normalized810ScaleZero_exists_fourthClearedDefect hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  have hconst :
      localClearedFifthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          lambda =
        Polynomial.C (eps * t ^ 35) := by
    rw [hV, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) eps (t ^ 35)).symm
  rw [hconst]
  exact (natDegree_C (eps * t ^ 35)).le

/-- Aligned/nonzero split of the scale-zero fourth defect: both constant
faces of `N` make the weight-`35` defect a ground constant, and neither
face is excluded or claimed closed. -/
theorem normalized810ScaleZero_fourthClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let N :=
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
    ∃ t : k, t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
      ((N = 0 ∧
          ∃ eps : k,
            localClearedFifthDefect810 (Polynomial.C t) (p.coeff 7)
                (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
                (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) 0 =
              Polynomial.C eps * (Polynomial.C t) ^ 35) ∨
        ∃ lambda eps : k, lambda ≠ 0 ∧
          N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
          localClearedFifthDefect810 (Polynomial.C t) (p.coeff 7)
              (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
              (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5) lambda =
            Polynomial.C eps * (Polynomial.C t) ^ 35) := by
  dsimp only
  obtain ⟨t, lambda, eps, ht, hHsq, hN, hV⟩ :=
    normalized810ScaleZero_exists_fourthClearedDefect hsource
  refine ⟨t, ht, hHsq, ?_⟩
  by_cases hlambda : lambda = 0
  · left
    refine ⟨?_, eps, ?_⟩
    · simpa [hlambda, map_zero, zero_mul] using hN
    · simpa [hlambda] using hV
  · exact Or.inr ⟨lambda, eps, hlambda, hN, hV⟩

/-- Source-facing aligned packet: if the discriminator vanishes, the
weight-`35` defect is still a ground constant.  The face is not
closed. -/
theorem normalized810ScaleZero_aligned_exists_fourthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t eps : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedFifthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          0 =
        Polynomial.C eps * (Polynomial.C t) ^ 35 := by
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
  obtain ⟨eps, hV⟩ :=
    scaleZero_alignedFourthClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hNzero)
  exact ⟨t, eps, ht, hHsq, by simpa only [p, q] using hV⟩

/-- Source-facing nonzero packet: if the discriminator is a nonzero
ground constant, the weight-`35` defect is still a ground constant.
The face is not closed. -/
theorem normalized810ScaleZero_nonzero_exists_fourthClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda eps : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedFifthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 3)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 5)
          lambda =
        Polynomial.C eps * (Polynomial.C t) ^ 35 := by
  obtain ⟨t, lambda, eps, ht, hHsq, hN, hV⟩ :=
    normalized810ScaleZero_exists_fourthClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro h0
    apply hNnonzero
    simpa [h0, map_zero, zero_mul] using hN
  exact ⟨t, lambda, eps, ht, hlambda, hHsq, hN, hV⟩

end ScaleZeroFourthDefect810

#print axioms normalized810ScaleZero_fifthCoefficientJacobianRow
#print axioms scaleZero_fifthCoefficientJacobianRow_810
#print axioms normalized810ScaleZero_fifthCoefficientJacobianRow_collapsed
#print axioms scaleZero_monicOcticDecic_degree12Row_810
#print axioms scaleZero_deltaResidual_deriv_zero_810
#print axioms scaleZero_fourthClearedDefect_exists_C_810
#print axioms scaleZero_alignedFourthClearedDefect_exists_C_810
#print axioms scaleZero_nonzeroFourthClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_fourthClearedDefect
#print axioms normalized810ScaleZero_fourthClearedDefect_natDegree_le_zero
#print axioms normalized810ScaleZero_fourthClearedDefectFirstFace
#print axioms normalized810ScaleZero_aligned_exists_fourthClearedDefect
#print axioms normalized810ScaleZero_nonzero_exists_fourthClearedDefect

end Max11DegreeRoutes
