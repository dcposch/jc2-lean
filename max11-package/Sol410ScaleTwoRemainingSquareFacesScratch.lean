import LowScale410ScaleZeroGammaFinalConeElimination
import Sol410ScaleTwoAlignedNonsquareTransverseEliminatedScratch

/-! # Exact remaining square-core faces of the normalized `(4,10)` route

Scale zero is already impossible.  At scale two the source discriminator
splits into its aligned and nonzero faces, and the aligned nonsquare chamber
is now impossible.  Consequently the entire unresolved `(4,10)` route is
the union of two source-honest square-core faces: aligned square and nonzero
square.  This file records that reduction and the final two-premise adapter;
it does not claim either remaining face is closed.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- Exclusion of the remaining aligned square-core `(4,10)` face. -/
def PlaneKeller410AlignedSquareExclusion
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (H h0 : K[X]),
    Normalized410LeadingCoreSource P Q H 2 → h0 ≠ 0 → H = h0 ^ 2 →
      (let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
       let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
       (5 : K[X]) * p.coeff 3 * H ^ 3 -
          (2 : K[X]) * q.coeff 9 = 0) → False

/-- Exclusion of the remaining nonzero square-core `(4,10)` face. -/
def PlaneKeller410NonzeroSquareExclusion
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (H h0 : K[X]) (lambda : K),
    Normalized410LeadingCoreSource P Q H 2 → h0 ≠ 0 → lambda ≠ 0 →
      H = h0 ^ 2 →
      (let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
       let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
       (5 : K[X]) * p.coeff 3 * H ^ 3 -
          (2 : K[X]) * q.coeff 9 = Polynomial.C lambda * h0 ^ 9) → False

/-- Every normalized scale-two `(4,10)` source lies on one of the two exact
remaining square-core faces.  The nonsquare aligned face is eliminated using
the same supplied source and discriminator; no witness is reselected. -/
theorem normalized410ScaleTwo_remainingSquareFaces
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {P Q : MvPolynomial (Fin 2) K} {H : K[X]}
    (hsource : Normalized410LeadingCoreSource P Q H 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    let N := (5 : K[X]) * p.coeff 3 * H ^ 3 -
      (2 : K[X]) * q.coeff 9
    (∃ h0 : K[X], h0 ≠ 0 ∧ H = h0 ^ 2 ∧ N = 0) ∨
      (∃ (h0 : K[X]) (lambda : K),
        h0 ≠ 0 ∧ lambda ≠ 0 ∧ H = h0 ^ 2 ∧
          N = Polynomial.C lambda * h0 ^ 9) := by
  dsimp only
  rcases normalized410ScaleTwo_discriminatorFirstFace hsource with
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
      exact (normalized410ScaleTwo_alignedNonsquare_false
        hsource hnonsquare haligned).elim
  · obtain ⟨h0, lambda, hh0, hlambda, hH, hN, _hlambdaSq⟩ :=
      squareCore_of_nonzero_imprimitiveRelation_410
        hsource.1 hkappa hrelation
    exact Or.inr ⟨h0, lambda, hh0, hlambda, hH, hN⟩

/-- Final routing adapter for `(4,10)`: the verified scale-zero exclusion and
aligned-nonsquare exclusion reduce the normalized low-scale route to exactly
the aligned-square and nonzero-square exclusions supplied as premises. -/
theorem planeKellerNormalized410LowScaleRoute_of_squareExclusions
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (haligned : PlaneKeller410AlignedSquareExclusion (K := K))
    (hnonzero : PlaneKeller410NonzeroSquareExclusion (K := K)) :
    PlaneKellerNormalized410LowScaleRoute (K := K) := by
  intro P Q H scale hscale hsource
  rcases hscale with rfl | htwo
  · exact (normalized410ScaleZero_impossible hsource).elim
  · subst scale
    rcases normalized410ScaleTwo_remainingSquareFaces hsource with
      ⟨h0, hh0, hH, hN⟩ | ⟨h0, lambda, hh0, hlambda, hH, hN⟩
    · exact (haligned P Q H h0 hsource hh0 hH hN).elim
    · exact (hnonzero P Q H h0 lambda hsource hh0 hlambda hH hN).elim

#print axioms normalized410ScaleTwo_remainingSquareFaces
#print axioms planeKellerNormalized410LowScaleRoute_of_squareExclusions

end Max11DegreeRoutes
