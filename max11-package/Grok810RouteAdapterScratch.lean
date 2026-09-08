import LowScale810ScaleTwoSourceFace

/-! # Route-assembly glue for the normalized `(8,10)` low-scale leaf

Untracked working note.  No tracked file was edited.

Scale zero is an explicit premise.  At scale two the source discriminator
splits into its aligned and nonzero faces.  The nonzero face carries a
linear local scale (`normalized810ScaleTwo_nonzeroFace_has_linear_root`):
`H = h0 ^ 2` with `H.natDegree = 2` forces `h0.natDegree = 1`, so `(8,10)`
has no multiple-root or no-root sub-chamber at this scale.  Consequently
the entire unresolved `(8,10)` route is the union of the scale-zero
exclusion, the aligned first-face, and the linear-root nonzero face.
This file records that three-premise adapter; it does not claim any of
those exclusions, and it does not close the route.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

/-- Exclusion of the normalized `(8,10)` scale-zero source. -/
def PlaneKeller810ScaleZeroExclusion
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (H : K[X]),
    Normalized810LeadingCoreSource P Q H 0 → False

/-- Exclusion of the aligned scale-two `(8,10)` first-face. -/
def PlaneKeller810AlignedFaceExclusion
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (H : K[X]),
    Normalized810LeadingCoreSource P Q H 2 →
      (let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
       let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
       (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) → False

/-- Exclusion of the nonzero scale-two `(8,10)` first-face, in the linear-root
packet of `normalized810ScaleTwo_nonzeroFace_has_linear_root`. -/
def PlaneKeller810NonzeroFaceExclusion
    {K : Type*} [Field K] : Prop :=
  ∀ (P Q : MvPolynomial (Fin 2) K) (H h0 : K[X]) (lambda a : K),
    Normalized810LeadingCoreSource P Q H 2 → h0 ≠ 0 →
      h0.natDegree = 1 → H = h0 ^ 2 → h0.eval a = 0 →
      (let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
       let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
       (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
         Polynomial.C lambda * h0 ^ 9) → lambda ≠ 0 → False

/-- Polynomial-level linear-root contradiction (the packet of
`piFace810_linearRoot_false_of_scaledPi_simplePole`, without its remaining
`hderiv` gap) implies the source-facing nonzero-face exclusion.  The Keller
bracket is converted with `bivariateJacobian_eq_C_of_keller`, as in
`normalized610ScaleTwo_nonzeroFace_false`. -/
theorem normalized810ScaleTwo_nonzeroFace_false_of_linearRootFalse
    {K : Type*} [Field K] [CharZero K]
    (hlinear :
      ∀ (p q : K[X][X]) (H h0 : K[X]) (j lambda a : K),
        p.natDegree = 8 → q.natDegree = 10 →
          h0 ≠ 0 → h0.natDegree = 1 → H = h0 ^ 2 →
          p.coeff 8 = H ^ 4 → q.coeff 10 = H ^ 5 →
          ((5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
            Polynomial.C lambda * h0 ^ 9) →
          (GCD369SourceXDeriv p * derivative q -
              derivative p * GCD369SourceXDeriv q =
            Polynomial.C (Polynomial.C j)) →
          h0.eval a = 0 → j ≠ 0 → False) :
    PlaneKeller810NonzeroFaceExclusion (K := K) := by
  intro P Q H h0 lambda a hsource hh0 hh0degree hH hroot hN _hlambda
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 =
      Polynomial.C lambda * h0 ^ 9 := by simpa only [p, q] using hN
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  exact hlinear p q H h0 j lambda a hp hq hh0 hh0degree hH hp8' hq10' hN'
    hD hroot hj

/-- Final routing adapter for `(8,10)`: the supplied scale-zero exclusion and
the two first-face exclusions reduce the normalized low-scale route to those
three premises.  This is `PlaneKellerNormalizedConsecutiveLowScaleRoute 4`.
No face is closed here. -/
theorem planeKellerNormalized810LowScaleRoute_of_faceExclusions
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (hzero : PlaneKeller810ScaleZeroExclusion (K := K))
    (haligned : PlaneKeller810AlignedFaceExclusion (K := K))
    (hnonzero : PlaneKeller810NonzeroFaceExclusion (K := K)) :
    PlaneKellerNormalized810LowScaleRoute (K := K) := by
  intro P Q H scale hscale hsource
  rcases hscale with rfl | htwo
  · exact (hzero P Q H hsource).elim
  · subst scale
    rcases normalized810ScaleTwo_discriminatorFirstFace hsource with
      hN0 | ⟨kappa, hkappa, hrelation⟩
    · exact (haligned P Q H hsource hN0).elim
    · have hNne :
          let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
          let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
          (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 ≠ 0 := by
        dsimp only
        intro hN0
        have hNsq_ne :
            ((5 : K[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial K).symm P).coeff 7 *
                  H -
              (4 : K[X]) *
                ((Polynomial.Bivariate.equivMvPolynomial K).symm Q).coeff 9) ^ 2 ≠
              0 := by
          rw [hrelation]
          exact mul_ne_zero (Polynomial.C_ne_zero.mpr hkappa)
            (pow_ne_zero 9 hsource.1)
        exact hNsq_ne (by simp [hN0])
      obtain ⟨h0, lambda, a, hh0, hlambda, hh0degree, hH, hroot, hN⟩ :=
        normalized810ScaleTwo_nonzeroFace_has_linear_root hsource hNne
      exact (hnonzero P Q H h0 lambda a hsource hh0 hh0degree hH hroot hN
        hlambda).elim

#print axioms normalized810ScaleTwo_nonzeroFace_false_of_linearRootFalse
#print axioms planeKellerNormalized810LowScaleRoute_of_faceExclusions

end Max11DegreeRoutes
