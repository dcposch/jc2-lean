import Grok610MultipleRootChamberScratch
import Grok610AlignedSquareFinalRowScratch

/-! # Exact remaining aligned faces of the normalized `(6,10)` route

Untracked working note.  No tracked file was edited.

Scale zero is an explicit premise.  At scale two the source discriminator
splits into its aligned and nonzero faces, and the nonzero face is now
impossible (`normalized610ScaleTwo_nonzeroFace_false`).  Consequently the
entire unresolved scale-two `(6,10)` route is the union of two source-honest
aligned faces: aligned square and aligned nonsquare.  This file records that
reduction and the three-premise adapter; it does not claim either remaining
face is closed, and it does not prove the scale-zero exclusion.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- Exclusion of the remaining aligned square-core `(6,10)` face. -/
def PlaneKeller610AlignedSquareExclusion
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (H h0 : K[X]),
    Normalized610LeadingCoreSource P Q H 2 → h0 ≠ 0 → H = h0 ^ 2 →
      (let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
       let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
       (5 : K[X]) * p.coeff 5 * H ^ 2 -
          (3 : K[X]) * q.coeff 9 = 0) → False

/-- Exclusion of the remaining aligned nonsquare `(6,10)` face. -/
def PlaneKeller610AlignedNonsquareExclusion
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (H : K[X]),
    Normalized610LeadingCoreSource P Q H 2 →
      (∀ h0 : K[X], H ≠ h0 ^ 2) →
      (let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
       let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
       (5 : K[X]) * p.coeff 5 * H ^ 2 -
          (3 : K[X]) * q.coeff 9 = 0) → False

/-- Every normalized scale-two `(6,10)` source lies on one of the two exact
remaining aligned faces.  The nonzero discriminator face is eliminated using
the same supplied source; no witness is reselected. -/
theorem normalized610ScaleTwo_remainingAlignedFaces
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (5 : K[X]) * p.coeff 5 * H ^ 2 -
      (3 : K[X]) * q.coeff 9
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧ N = 0) ∨
      ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧ N = 0) := by
  dsimp only
  rcases normalized610ScaleTwo_discriminatorFirstFace hsource with
    haligned | ⟨kappa, hkappa, hrelation⟩
  · by_cases hsquare : ∃ h0 : K[X], H = h0 ^ 2
    · obtain ⟨h0, hH⟩ := hsquare
      have hh0 : h0 ≠ 0 := by
        intro hzero
        apply hsource.1
        rw [hH, hzero]
        simp
      exact Or.inl ⟨h0, hh0, hH, haligned⟩
    · have hnonsquare : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
        intro h0 hH
        exact hsquare ⟨h0, hH⟩
      exact Or.inr ⟨hnonsquare, haligned⟩
  · have hnonzero :
        let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
        let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
        (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 ≠ 0 := by
      dsimp only
      intro hN0
      have hNsq_ne :
          ((5 : K[X]) *
              ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 5 *
                H ^ 2 -
            (3 : K[X]) *
              ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 9) ^ 2 ≠
            0 := by
        rw [hrelation]
        exact mul_ne_zero (Polynomial.C_ne_zero.mpr hkappa)
          (pow_ne_zero 9 hsource.1)
      exact hNsq_ne (by simp [hN0])
    exact (normalized610ScaleTwo_nonzeroFace_false hsource hnonzero).elim

/-- Final routing adapter for `(6,10)`: the supplied scale-zero exclusion and
the two remaining aligned exclusions reduce the normalized low-scale route
to those three premises.  The nonzero discriminator face is already closed. -/
theorem planeKellerNormalized610LowScaleRoute_of_alignedExclusions
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hzero : ∀ (P Q : MvPolynomial (Fin 2) K) (H : K[X]),
      Normalized610LeadingCoreSource P Q H 0 → False)
    (hsquare : PlaneKeller610AlignedSquareExclusion (K := K))
    (hnonsquare : PlaneKeller610AlignedNonsquareExclusion (K := K)) :
    PlaneKellerNormalized610LowScaleRoute (K := K) := by
  intro P Q H scale hscale hsource
  rcases hscale with rfl | htwo
  · exact (hzero P Q H hsource).elim
  · subst scale
    rcases normalized610ScaleTwo_remainingAlignedFaces hsource with
      ⟨h0, hh0, hH, hN⟩ | ⟨hnonsquareH, hN⟩
    · exact (hsquare P Q H h0 hsource hh0 hH hN).elim
    · exact (hnonsquare P Q H hsource hnonsquareH hN).elim

#print axioms normalized610ScaleTwo_nonzeroFace_false
#print axioms normalized610ScaleTwo_alignedSquare_exhaustedPacket
#print axioms normalized610ScaleTwo_alignedNonsquare_openPacket
#print axioms normalized610ScaleTwo_remainingAlignedFaces
#print axioms planeKellerNormalized610LowScaleRoute_of_alignedExclusions

end Max11DegreeRoutes
