import LowScale810ScaleZeroSource
import LowScale810ScaleTwoThirdFace

/-! # Scale-zero second defect for the normalized `(8,10)`, `H = 0` leaf

The source packet already makes the discriminator `N` a ground-field
constant and, after a square root of the core, clears the first
octic/decic defect to a ground constant times `h¹⁴`.  This file consumes
the next Keller coefficient of the same monic octic-decic depression:
the degree-`14` Jacobian row is `10 B' + 9 L A' - 8 Q' = 0`.  The
corresponding cleared polynomial defect of weight twenty-one is likewise
a ground-field constant.

Both constant faces of `N` are treated honestly: the vanishing face
`λ = 0` and the nonzero constant face use the same ninth-power clearing,
and neither is claimed closed.  Root-evaluation from the scale-two third
face is unavailable, because a nonzero constant has no finite root.

No total-degree or twice-prime theorem is used.  The packet does not
close the leaf: the next missing input is the degree-`13` residual of
the same monic depression.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

section ScaleZeroSecondDefect810

variable {k : Type*} [Field k] [CharZero k]

/-! ## Degree-`14` monic Jacobian row -/

/-- For a monic octic and a monic decic whose `z⁹` coefficient `L` is
already a differential constant, the degree-`14` Jacobian coefficient
is exactly `10 B' + 9 L A' - 8 Q'`.  Here `A = f.coeff 6`,
`B = f.coeff 5`, `L = g.coeff 9`, and `Q = g.coeff 7`. -/
theorem scaleZero_monicOcticDecic_degree14Row_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (f g : F[X])
    (hf_high : ∀ n, 8 < n → f.coeff n = 0) (hf8 : f.coeff 8 = 1)
    (hf7 : f.coeff 7 = 0)
    (hg_high : ∀ n, 10 < n → g.coeff n = 0) (hg10 : g.coeff 10 = 1)
    (hL : d (g.coeff 9) = 0) :
    (differentialJacobian d f g).coeff 14 =
      (10 : F) * d (f.coeff 5) + (9 : F) * g.coeff 9 * d (f.coeff 6) -
        (8 : F) * d (g.coeff 7) :=
  differentialJacobian_coeff_14_monicOcticDecic d f g hf_high hf8 hf7
    hg_high hg10 hL

/-- The same row integrates: if `10 B' + 9 L A' - 8 Q' = 0` and `L` is
constant, then the first residual `Q - (5/4) B - (9/8) L A` is a
differential constant. -/
theorem scaleZero_betaResidual_deriv_zero_810
    {F : Type*} [Field F] [Algebra k F] [CharZero F]
    (d : Derivation k F F) (L A B Q : F)
    (hL : d L = 0)
    (hrow : (10 : F) * d B + (9 : F) * L * d A - (8 : F) * d Q = 0) :
    d (betaResidual810 L A B Q) = 0 :=
  betaResidual810_deriv_zero d L A B Q hL hrow

/-! ## Cleared weight-`21` defect on a constant square core -/

/-- On a constant square core the source discriminator is a scalar times
`h⁹`, so the existing ninth-power identities apply with a constant
square root on both the vanishing face `λ = 0` and the nonzero
constant face. -/
theorem scaleZero_secondClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5) :
    ∃ (lambda gamma : k),
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
          Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedThirdDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda =
        Polynomial.C gamma * (Polynomial.C t) ^ 21 := by
  have hjac : bivariateJacobian p q = Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hD
  obtain ⟨lambda, hN⟩ :=
    scaleZero_discriminator_eq_C_mul_ninthPower_810 hp hq hjac ht hH hp8 hq10
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨gamma, hgamma⟩ :=
    nonzeroFace810_thirdDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨lambda, gamma, hN, hgamma⟩

/-- Aligned constant face `N = 0`: the same degree-`14` clearing applies
with `λ = 0`, and the weight-`21` defect is still a ground constant.
This does not close the face. -/
theorem scaleZero_alignedSecondClearedDefect_exists_C_810
    {p q : k[X][X]} {j t : k} {H : k[X]}
    (hp : p.natDegree = 8) (hq : q.natDegree = 10)
    (hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j))
    (ht : t ≠ 0) (hH : H = (Polynomial.C t) ^ 2)
    (hp8 : p.coeff 8 = H ^ 4) (hq10 : q.coeff 10 = H ^ 5)
    (hN : (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 = 0) :
    ∃ gamma : k,
      localClearedThirdDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (q.coeff 8) (q.coeff 7) 0 =
        Polynomial.C gamma * (Polynomial.C t) ^ 21 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  have hN0 :
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9 =
        Polynomial.C (0 : k) * (Polynomial.C t) ^ 9 := by
    simpa [map_zero, zero_mul] using hN
  obtain ⟨gamma, hgamma⟩ :=
    nonzeroFace810_thirdDefectPowerRelation p q H (Polynomial.C t) j 0
      hp hq hh0 hH hp8 hq10 hN0 hD
  exact ⟨gamma, hgamma⟩

/-- Nonzero constant face: `N` is a nonzero scalar times `h⁹`, and the
weight-`21` defect is a ground constant.  This does not close the
face. -/
theorem scaleZero_nonzeroSecondClearedDefect_exists_C_810
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
    ∃ gamma : k,
      localClearedThirdDefect810 (Polynomial.C t) (p.coeff 7) (p.coeff 6)
          (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda =
        Polynomial.C gamma * (Polynomial.C t) ^ 21 := by
  have hh0 : (Polynomial.C t : k[X]) ≠ 0 := Polynomial.C_ne_zero.mpr ht
  obtain ⟨gamma, hgamma⟩ :=
    nonzeroFace810_thirdDefectPowerRelation p q H (Polynomial.C t) j lambda
      hp hq hh0 hH hp8 hq10 hN hD
  exact ⟨gamma, hgamma⟩

variable [IsAlgClosed k]

/-- Source-facing second residual packet for a normalized scale-zero
`(8,10)` pair: after a square root of the core, the cleared weight-`21`
defect is a ground-field constant. -/
theorem normalized810ScaleZero_exists_secondClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda gamma : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedThirdDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          lambda =
        Polynomial.C gamma * (Polynomial.C t) ^ 21 := by
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
  obtain ⟨lambda, gamma, hN, hT⟩ :=
    scaleZero_secondClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
  exact ⟨t, lambda, gamma, ht, hHsq, by simpa only [p, q] using hN,
    by simpa only [p, q] using hT⟩

/-- Newton degree of the second cleared octic/decic defect at scale
zero. -/
theorem normalized810ScaleZero_secondClearedDefect_natDegree_le_zero
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    ∃ (t lambda : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (localClearedThirdDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          lambda).natDegree ≤ 0 := by
  obtain ⟨t, lambda, gamma, ht, hHsq, _hN, hT⟩ :=
    normalized810ScaleZero_exists_secondClearedDefect hsource
  refine ⟨t, lambda, ht, hHsq, ?_⟩
  have hconst :
      localClearedThirdDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          lambda =
        Polynomial.C (gamma * t ^ 21) := by
    rw [hT, ← Polynomial.C_pow]
    exact (map_mul (Polynomial.C : k →+* k[X]) gamma (t ^ 21)).symm
  rw [hconst]
  exact (natDegree_C (gamma * t ^ 21)).le

/-- Aligned/nonzero split of the scale-zero second defect: both constant
faces of `N` make the weight-`21` defect a ground constant, and neither
face is excluded or claimed closed. -/
theorem normalized810ScaleZero_secondClearedDefectFirstFace
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial k).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial k).symm Q
    let N :=
      (5 : k[X]) * p.coeff 7 * H - (4 : k[X]) * q.coeff 9
    ∃ t : k, t ≠ 0 ∧ H = (Polynomial.C t) ^ 2 ∧
      ((N = 0 ∧
          ∃ gamma : k,
            localClearedThirdDefect810 (Polynomial.C t) (p.coeff 7)
                (p.coeff 6) (p.coeff 5) (q.coeff 8) (q.coeff 7) 0 =
              Polynomial.C gamma * (Polynomial.C t) ^ 21) ∨
        ∃ lambda gamma : k, lambda ≠ 0 ∧
          N = Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
          localClearedThirdDefect810 (Polynomial.C t) (p.coeff 7)
              (p.coeff 6) (p.coeff 5) (q.coeff 8) (q.coeff 7) lambda =
            Polynomial.C gamma * (Polynomial.C t) ^ 21) := by
  dsimp only
  obtain ⟨t, lambda, gamma, ht, hHsq, hN, hT⟩ :=
    normalized810ScaleZero_exists_secondClearedDefect hsource
  refine ⟨t, ht, hHsq, ?_⟩
  by_cases hlambda : lambda = 0
  · left
    refine ⟨?_, gamma, ?_⟩
    · simpa [hlambda, map_zero, zero_mul] using hN
    · simpa [hlambda] using hT
  · exact Or.inr ⟨lambda, gamma, hlambda, hN, hT⟩

/-- Source-facing aligned packet: if the discriminator vanishes, the
weight-`21` defect is still a ground constant.  The face is not
closed. -/
theorem normalized810ScaleZero_aligned_exists_secondClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        0) :
    ∃ (t gamma : k),
      t ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      localClearedThirdDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          0 =
        Polynomial.C gamma * (Polynomial.C t) ^ 21 := by
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
  obtain ⟨gamma, hT⟩ :=
    scaleZero_alignedSecondClearedDefect_exists_C_810 hp hq hD ht hHsq
      (by simpa only [p] using hp8) (by simpa only [q] using hq10)
      (by simpa only [p, q] using hNzero)
  exact ⟨t, gamma, ht, hHsq, by simpa only [p, q] using hT⟩

/-- Source-facing nonzero packet: if the discriminator is a nonzero
ground constant, the weight-`21` defect is still a ground constant.
The face is not closed. -/
theorem normalized810ScaleZero_nonzero_exists_secondClearedDefect
    {P Q : MvPolynomial (Fin 2) k} {H : k[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 0)
    (hNnonzero :
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 ≠
        0) :
    ∃ (t lambda gamma : k),
      t ≠ 0 ∧
      lambda ≠ 0 ∧
      H = (Polynomial.C t) ^ 2 ∧
      (5 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7 *
            H -
        (4 : k[X]) *
          ((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 9 =
        Polynomial.C lambda * (Polynomial.C t) ^ 9 ∧
      localClearedThirdDefect810 (Polynomial.C t)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 7)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 6)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm P).coeff 5)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 8)
          (((Polynomial.Bivariate.equivMvPolynomial k).symm Q).coeff 7)
          lambda =
        Polynomial.C gamma * (Polynomial.C t) ^ 21 := by
  obtain ⟨t, lambda, gamma, ht, hHsq, hN, hT⟩ :=
    normalized810ScaleZero_exists_secondClearedDefect hsource
  have hlambda : lambda ≠ 0 := by
    intro h0
    apply hNnonzero
    simpa [h0, map_zero, zero_mul] using hN
  exact ⟨t, lambda, gamma, ht, hlambda, hHsq, hN, hT⟩

end ScaleZeroSecondDefect810

#print axioms scaleZero_monicOcticDecic_degree14Row_810
#print axioms scaleZero_betaResidual_deriv_zero_810
#print axioms scaleZero_secondClearedDefect_exists_C_810
#print axioms scaleZero_alignedSecondClearedDefect_exists_C_810
#print axioms scaleZero_nonzeroSecondClearedDefect_exists_C_810
#print axioms normalized810ScaleZero_exists_secondClearedDefect
#print axioms normalized810ScaleZero_secondClearedDefect_natDegree_le_zero
#print axioms normalized810ScaleZero_secondClearedDefectFirstFace
#print axioms normalized810ScaleZero_aligned_exists_secondClearedDefect
#print axioms normalized810ScaleZero_nonzero_exists_secondClearedDefect

end Max11DegreeRoutes
