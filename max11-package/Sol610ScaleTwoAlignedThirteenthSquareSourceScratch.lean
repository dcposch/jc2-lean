import Sol610ScaleTwoAlignedThirteenthSquareScratch

/-! # Source-facing odd successor for the aligned `(6,10)` square chamber

This wrapper selects the second-defect constant once from the normalized
Keller source, then threads that exact witness through the verified weight-30
row and the square-chamber weight-65 clearing.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000

/-- A normalized aligned square source supplies one common `κ` together with
its successive weight-30 and weight-65 first integrals. -/
theorem normalized610ScaleTwo_alignedThirteenthSquareSource_610
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ κ c xi : K,
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
          Polynomial.C κ * H ^ 5 ∧
      alignedTwelfthDefect610 H (p.coeff 5) (p.coeff 4) (p.coeff 3)
          (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8) (q.coeff 7)
          (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3) (q.coeff 2)
          (q.coeff 1) =
        Polynomial.C c * H ^ 30 ∧
      localClearedThirteenthDefect610 h0 (p.coeff 5) (p.coeff 4)
          (p.coeff 3) (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 8)
          (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
          (q.coeff 2) (q.coeff 1) 0 =
        Polynomial.C xi * h0 ^ 65 := by
  dsimp only at haligned ⊢
  have hsrc := hsource
  rcases hsrc with
    ⟨hH, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  obtain ⟨κ, hM⟩ :=
    alignedSecondDefectPowerRelation_610 hp hq hjac hH hp6' hq10'
      haligned
  obtain ⟨c, xi, hthirty, hsixtyfive⟩ :=
    normalized610ScaleTwo_alignedThirteenthSquarePowerRelation_610 hsource
      haligned hM hh0 hHsq
  exact ⟨κ, c, xi, hM, hthirty, hsixtyfive⟩

#print axioms normalized610ScaleTwo_alignedThirteenthSquareSource_610

end Max11DegreeRoutes
