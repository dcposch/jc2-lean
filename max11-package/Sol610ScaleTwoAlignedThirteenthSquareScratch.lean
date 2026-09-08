import Sol610ScaleTwoAlignedTwelfthSourceScratch
import Fable610ScaleZeroTwelfthDefectScratch

/-! # The odd weight-65 successor on the aligned `(6,10)` square chamber

The source-assembled aligned twelfth row gives the chamber-free weight-30
integral.  On a square presentation `H = h₀²`, the already verified generic
degree-2 sextic/decic calculation applies to that very same normalized source
with discriminator parameter zero.  Thus its next integral has odd cleared
weight 65.  The statement retains the weight-30 witness alongside the new
weight-65 witness so neither source nor earlier integration data is reselected.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 100000

/-- Same-source square-chamber packet for the two successive aligned
`(6,10)` integrals of weights `30` and `65/2`. -/
theorem normalized610ScaleTwo_alignedThirteenthSquarePowerRelation_610
    {K : Type*} [Field K] [CharZero K]
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]} {κ : K}
    (hsource : Normalized610LeadingCoreSource P Q H 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 = 0)
    (hM :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      alignedSecondDefect610 H (p.coeff 4) (p.coeff 5) (q.coeff 8) =
        Polynomial.C κ * H ^ 5)
    (hh0 : h0 ≠ 0) (hH : H = h0 ^ 2) :
    let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
    let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
    ∃ c xi : K,
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
  dsimp only at haligned hM ⊢
  have hthirty :=
    normalized610ScaleTwo_alignedTwelfthDefectPowerRelation_610 hsource
      haligned hM
  dsimp only at hthirty
  rcases hsource with
    ⟨_hHsource, _hHdegree, hPdegree, hQdegree, hp6, hq10, hKeller⟩
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hp : p.natDegree = 6 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp6' : p.coeff 6 = H ^ 3 := by simpa only [p] using hp6
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  obtain ⟨j, _hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD :
      GCD369SourceXDeriv p * derivative q -
          derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  have hN :
      (5 : K[X]) * p.coeff 5 * H ^ 2 - (3 : K[X]) * q.coeff 9 =
        Polynomial.C (0 : K) * h0 ^ 9 := by
    simpa only [map_zero, zero_mul] using haligned
  obtain ⟨xi, hxi⟩ :=
    nonzeroFace610_thirteenthDefectPowerRelation p q H h0 j 0 hp hq hh0
      hH hp6' hq10' hN hD
  rcases hthirty with ⟨c, hc⟩
  exact ⟨c, xi, hc, hxi⟩

#print axioms normalized610ScaleTwo_alignedThirteenthSquarePowerRelation_610

end Max11DegreeRoutes
