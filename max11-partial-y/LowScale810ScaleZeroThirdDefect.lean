import LowScale810ScaleZeroSecondDefect
import LowScale810ScaleTwoFourthFace

/-! # Scale-zero third defect for the normalized `(8,10)`, `H = 0` leaf

The second-defect packet already makes the discriminator `N` a
ground-field constant and, after a square root of the core, clears the
first two octic/decic defects to ground constants times `h¹⁴` and
`h²¹`.  This file consumes the next Keller coefficient of the same
monic octic-decic depression: the degree-`13` Jacobian row is
`10 C' + 9 L B' + 8 P A' - 6 A P' - 8 R' = 0`.  The corresponding
cleared polynomial defect of weight twenty-eight is likewise a
ground-field constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  Root-evaluation from the scale-two
fourth face is unavailable, because a nonzero constant has no finite
root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`12` residual of
the same monic depression.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ScaleZeroThirdDefect810

variable {k : Type*} [Field k] [CharZero k]

/-! ## Degree-`13` monic Jacobian row -/

/-- For a monic octic and a monic decic whose `z⁹` coefficient `L` is
already a differential constant, the degree-`13` Jacobian coefficient
is exactly `10 C' + 9 L B' + 8 P A' - 6 A P' - 8 R'`.  Here
`A = f.coeff 6`, `B = f.coeff 5`, `C = f.coeff 4`, `L = g.coeff 9`,
`P = g.coeff 8`, and `R = g.coeff 6`. -/
theorem scaleZero_monicOcticDecic_degree13Row_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 13 =
      (10 : F) * d (f.coeff 4) + (9 : F) * g.coeff 9 * d (f.coeff 5) +
        (8 : F) * g.coeff 8 * d (f.coeff 6) -
          (6 : F) * f.coeff 6 * d (g.coeff 8) -
          (8 : F) * d (g.coeff 6) :=
  differentialJacobian_coeff_13_monicOcticDecic d f g hf_high hf8 hf7
    hg_high hg10 hL

/-- The same row integrates: if `10 C' + 9 L B' + 8 P A' - 6 A P' - 8 R' = 0`,
`L` is constant, and the second-face residual `P - (5/4) A` is constant,
then the first residual
`R - (5/4) C - (5/32) A² - (9/8) L B - α A` is a differential constant. -/
theorem scaleZero_gammaResidual_deriv_zero_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (L A B C0 P R : F)
    (hL : d L = 0)
    (halpha : d (alphaResidual810 A P) = 0)
    (hrow : (10 : F) * d C0 + (9 : F) * L * d B +
        (8 : F) * P * d A - (6 : F) * A * d P -
        (8 : F) * d R = 0) :
    d (gammaResidual810 L A B C0 P R) = 0 :=
  gammaResidual810_deriv_zero d L A B C0 P R hL halpha hrow

/-! ## Cleared weight-`28` defect on a constant square core -/

/-- On a constant square core the source discriminator is a scalar times
`h⁹`, so the existing ninth-power identities apply with a constant
square root on both the vanishing face `λ = 0` and the nonzero
constant face. -/
theorem scaleZero_thirdClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda delta : k),
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedFourthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          lambda =
        Polynomial.C delta * (Polynomial.C t) ^ 28 := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  obtain ⟨lambda, hN⟩ :=
    scaleZero_discriminator_eq_C_mul_ninthPower_810 hp hq hjac ht hH hp8 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨delta, hdelta⟩ :=
    nonzeroFace810_fourthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨lambda, delta, hN, hdelta⟩

/-- Aligned constant face `N = 0`: the same degree-`13` clearing applies
with `λ = 0`, and the weight-`28` defect is still a ground constant.
This does not close the face. -/
theorem scaleZero_alignedThirdClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0) :
    ∃ delta : k,
      localClearedFourthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (q.coeff 8) (q.coeff 7) (q.coeff 6) 0 =
        Polynomial.C delta * (Polynomial.C t) ^ 28 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hN0 :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C (0 : k) * (Polynomial.C t) ^ 9 := by
    simpa [map_zero, zero_mul] using hN
  obtain ⟨delta, hdelta⟩ :=
    nonzeroFace810_fourthDefectPowerRelation p q H (Polynomial.C t) j 0
      hp hq hh0 hH hp8 hq10 hN0 hD
  exact ⟨delta, hdelta⟩

/-- Nonzero constant face: `N` is a nonzero scalar times `h⁹`, and the
weight-`28` defect is a ground constant.  This does not close the
face. -/
theorem scaleZero_nonzeroThirdClearedDefect_exists_C_810
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
    ∃ delta : k,
      localClearedFourthDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (p.coeff 4) (q.coeff 8) (q.coeff 7) (q.coeff 6)
          lambda =
        Polynomial.C delta * (Polynomial.C t) ^ 28 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨delta, hdelta⟩ :=
    nonzeroFace810_fourthDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨delta, hdelta⟩

variable [IsAlgClosed k]

/-- Source-facing third residual packet for a normalized scale-zero
`(8,10)` pair: after a square root of the core, the cleared weight-`28`
defect is a ground-field constant. -/
theorem normalized810ScaleZero_exists_thirdClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda delta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedFourthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          lambda =
        Polynomial.C delta * (Polynomial.C t) ^ 28 := by
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
  obtain ⟨lambda, delta, hN, hU⟩ :=
    scaleZero_thirdClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
  exact ⟨t, lambda, delta, ht, hHsq, by simpa only [p, q] using hN,
    by simpa only [p, q] using hU⟩

/-- Newton degree of the third cleared octic/decic defect at scale
zero. -/
theorem normalized810ScaleZero_thirdClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedFourthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, delta, ht, hHsq, _hN, hU⟩ :=
    normalized810ScaleZero_exists_thirdClearedDefect hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  have hconst :
      localClearedFourthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          lambda =
        Polynomial.C (delta * t ^ 28) := by
    rw [hU, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) delta (t ^ 28)).symm
  rw [hconst]
  exact (natDegree_C (delta * t ^ 28)).le

/-- Aligned/nonzero split of the scale-zero third defect: both constant
faces of `N` make the weight-`28` defect a ground constant, and neither
face is excluded or claimed closed. -/
theorem normalized810ScaleZero_thirdClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let N :=
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
    ∃ t : k, t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
      ((N = 0 ∧
          ∃ delta : k,
            localClearedFourthDefect810 (Polynomial.C t) (p.coeff 7)
                (p.coeff 6) (p.coeff 5) (p.coeff 4) (q.coeff 8)
                (q.coeff 7) (q.coeff 6) 0 =
              Polynomial.C delta * (Polynomial.C t) ^ 28) ∨
        ∃ lambda delta : k, lambda ≠ 0 ∧
          N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
          localClearedFourthDefect810 (Polynomial.C t) (p.coeff 7)
              (p.coeff 6) (p.coeff 5) (p.coeff 4) (q.coeff 8)
              (q.coeff 7) (q.coeff 6) lambda =
            Polynomial.C delta * (Polynomial.C t) ^ 28) := by
  dsimp only
  obtain ⟨t, lambda, delta, ht, hHsq, hN, hU⟩ :=
    normalized810ScaleZero_exists_thirdClearedDefect hsource
  refine ⟨t, ht, hHsq, ?_⟩
  by_cases hlambda : lambda = 0
  · left
    refine ⟨?_, delta, ?_⟩
    · simpa [hlambda, map_zero, zero_mul] using hN
    · simpa [hlambda] using hU
  · exact Or.inr ⟨lambda, delta, hlambda, hN, hU⟩

/-- Source-facing aligned packet: if the discriminator vanishes, the
weight-`28` defect is still a ground constant.  The face is not
closed. -/
theorem normalized810ScaleZero_aligned_exists_thirdClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t delta : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedFourthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          0 =
        Polynomial.C delta * (Polynomial.C t) ^ 28 := by
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
  obtain ⟨delta, hU⟩ :=
    scaleZero_alignedThirdClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hNzero)
  exact ⟨t, delta, ht, hHsq, by simpa only [p, q] using hU⟩

/-- Source-facing nonzero packet: if the discriminator is a nonzero
ground constant, the weight-`28` defect is still a ground constant.
The face is not closed. -/
theorem normalized810ScaleZero_nonzero_exists_thirdClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda delta : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedFourthDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 4)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 6)
          lambda =
        Polynomial.C delta * (Polynomial.C t) ^ 28 := by
  obtain ⟨t, lambda, delta, ht, hHsq, hN, hU⟩ :=
    normalized810ScaleZero_exists_thirdClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro h0
    apply hNnonzero
    simpa [h0, map_zero, zero_mul] using hN
  exact ⟨t, lambda, delta, ht, hlambda, hHsq, hN, hU⟩

end ScaleZeroThirdDefect810

#print axioms scaleZero_monicOcticDecic_degree13Row_810
#print axioms scaleZero_gammaResidual_deriv_zero_810
#print axioms scaleZero_thirdClearedDefect_exists_C_810
#print axioms scaleZero_alignedThirdClearedDefect_exists_C_810
#print axioms scaleZero_nonzeroThirdClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_thirdClearedDefect
#print axioms normalized810ScaleZero_thirdClearedDefect_natDegree_le_zero
#print axioms normalized810ScaleZero_thirdClearedDefectFirstFace
#print axioms normalized810ScaleZero_aligned_exists_thirdClearedDefect
#print axioms normalized810ScaleZero_nonzero_exists_thirdClearedDefect

end Max11DegreeRoutes
