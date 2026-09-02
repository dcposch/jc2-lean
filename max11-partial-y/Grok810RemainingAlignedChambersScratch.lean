import Grok810RouteAdapterScratch

/-! # Remaining aligned chambers of the normalized `(8,10)` route

Untracked working note.  No tracked file was edited.

Scale zero is an explicit premise.  At scale two the source discriminator
splits into its aligned and nonzero faces
(`planeKellerNormalized810LowScaleRoute_of_faceExclusions`).  The aligned
face `PlaneKeller810AlignedFaceExclusion` carries no local scale `h0`, so
this file splits it into the two source-honest chambers: aligned square
(`H = h0 ^ 2`) and aligned nonsquare (`∀ h0, H ≠ h0 ^ 2`).  The four-premise
adapter is the existing three-premise route with that split substituted for
`haligned`.  Neither remaining aligned chamber is claimed closed, the
nonzero face is not claimed closed, and the scale-zero exclusion is not
proved.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- Exclusion of the remaining aligned square-core `(8,10)` chamber. -/
def PlaneKeller810AlignedSquareExclusion
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (H h0 : K[X]),
    Normalized810LeadingCoreSource P Q H 2 → h0 ≠ 0 → H = h0 ^ 2 →
      (let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
       let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
       (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) → False

/-- Exclusion of the remaining aligned nonsquare `(8,10)` chamber. -/
def PlaneKeller810AlignedNonsquareExclusion
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (H : K[X]),
    Normalized810LeadingCoreSource P Q H 2 →
      (∀ h0 : K[X], H ≠ h0 ^ 2) →
      (let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
       let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
       (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) → False

/-- Scale two of a square core forces the local scale to be linear.
`H.natDegree = 2` and `H = h0 ^ 2` give `h0.natDegree = 1` by
`Polynomial.natDegree_pow`. -/
theorem alignedSquare810_h0_natDegree_eq_one
    {K : Type*} [Field K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) :
    h0.natDegree = 1 := by
  have h2 : (h0 ^ 2).natDegree = 2 := by
    rw [← hHsq]
    exact hsource.2.1
  rw [Polynomial.natDegree_pow] at h2
  omega

/-- Every aligned scale-two `(8,10)` source lies on one of the two exact
remaining aligned chambers.  The square witness is nonzero because the
supplied source has `H ≠ 0`. -/
theorem normalized810ScaleTwo_remainingAlignedChambers
    {K : Type*} [Field K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧ N = 0) ∨
      ((∀ h0 : K[X], H ≠ h0 ^ 2) ∧ N = 0) := by
  dsimp only
  by_cases hsq : ∃ h0 : K[X], H = h0 ^ 2
  · obtain ⟨h0, hH⟩ := hsq
    have hh0 : h0 ≠ 0 := by
      intro hzero
      apply hsource.1
      rw [hH, hzero]
      simp
    exact Or.inl ⟨h0, hh0, hH, haligned⟩
  · have hnonsquare : ∀ h0 : K[X], H ≠ h0 ^ 2 := by
      intro h0 hH
      exact hsq ⟨h0, hH⟩
    exact Or.inr ⟨hnonsquare, haligned⟩

/-- The two remaining aligned-chamber exclusions reassemble the aligned
first-face exclusion consumed by
`planeKellerNormalized810LowScaleRoute_of_faceExclusions`. -/
theorem planeKeller810AlignedFaceExclusion_of_chambers
    {K : Type*} [Field K]
    (hsquare : PlaneKeller810AlignedSquareExclusion (K := K))
    (hnonsquare : PlaneKeller810AlignedNonsquareExclusion (K := K)) :
    PlaneKeller810AlignedFaceExclusion (K := K) := by
  intro P Q H hsource hN
  rcases normalized810ScaleTwo_remainingAlignedChambers hsource hN with
    ⟨h0, hh0, hH, hN'⟩ | ⟨hnonsquareH, hN'⟩
  · exact hsquare P Q H h0 hsource hh0 hH hN'
  · exact hnonsquare P Q H hsource hnonsquareH hN'

/-- Final routing adapter for `(8,10)`: the supplied scale-zero exclusion,
the nonzero first-face exclusion, and the two remaining aligned-chamber
exclusions reduce the normalized low-scale route to those four premises.
No face or chamber is closed here. -/
theorem planeKellerNormalized810LowScaleRoute_of_chamberExclusions
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hzero : PlaneKeller810ScaleZeroExclusion (K := K))
    (hnonzero : PlaneKeller810NonzeroFaceExclusion (K := K))
    (hsquare : PlaneKeller810AlignedSquareExclusion (K := K))
    (hnonsquare : PlaneKeller810AlignedNonsquareExclusion (K := K)) :
    PlaneKellerNormalized810LowScaleRoute (K := K) :=
  planeKellerNormalized810LowScaleRoute_of_faceExclusions hzero
    (planeKeller810AlignedFaceExclusion_of_chambers hsquare hnonsquare)
    hnonzero

#print axioms alignedSquare810_h0_natDegree_eq_one
#print axioms normalized810ScaleTwo_remainingAlignedChambers
#print axioms planeKeller810AlignedFaceExclusion_of_chambers
#print axioms planeKellerNormalized810LowScaleRoute_of_chamberExclusions

end Max11DegreeRoutes
