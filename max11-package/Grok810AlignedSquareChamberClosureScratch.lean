import Grok810AlignedSquareClearedNumeratorGlueScratch

/-! # CLOSED. Source-facing closure of the `(8,10)` scale-two aligned-square chamber

Lane Z of `Grok810AlignedFaceTowerPlanScratch.md`.  Untracked working
note.  No tracked file was edited.

Parents (tracked, green):

* `Grok810AlignedSquareClearedNumeratorGlueScratch`
  (`alignedSquareClearedNumerator810_algebraMap_eq_pow_scaledPrimitive`,
  `alignedSquarePrimitive810_scaledDeriv_eq_simplePole_of_source`,
  `alignedSquareFace810_order119Ceiling`);
* `Grok810AlignedSquareSourceWrapperScratch` (via Glue)
  (bookkeeping `alignedSquareSourceClearingPower810` /
  `alignedSquareRemainingPole810`, both `119`);
* `Grok810RemainingAlignedChambersScratch` (via Glue)
  (`PlaneKeller810AlignedSquareExclusion`,
  `alignedSquare810_h0_natDegree_eq_one`).

The aligned-square source `N = 0`, `H = h0^2` supplies the pole-`119`
numerator of the scaled primitive, whose derivative is the genuine
simple pole `C(2^{62} j)/h0`.  The order-`119` ceiling is then False.

**CLOSED:** `alignedSquareFace810_squareChamber`.
**CLOSED:** `normalized810ScaleTwo_alignedSquare_false`.
**CLOSED:** `planeKeller810AlignedSquareExclusion_closed`.

There is no unused compact-numerator order after `119`.  The aligned
nonsquare chamber is not opened.

No `sorry`, no new axioms, no finite-root shortcut, no closure overclaim.
-/

open scoped Polynomial.Bivariate

noncomputable section

open MvPolynomial Polynomial

namespace Max11DegreeRoutes

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

set_option maxRecDepth 1000000
set_option maxHeartbeats 800000000

/-! ## Chamber closure on the raw square-core hypotheses -/

section AlignedSquareChamber810

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

set_option maxHeartbeats 800000000 in
/-- **CLOSED.** Source-facing joint packet of the `(8,10)` aligned-square
chamber.  The wrapper supplies the genuine simple pole; the clearing
identity supplies the pole-`119` numerator of the scaled primitive; the
order-`119` ceiling is then False. -/
theorem alignedSquareFace810_squareChamber
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    False := by
  dsimp only at haligned
  let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
  let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
  have hdegree : h0.natDegree = 1 :=
    alignedSquare810_h0_natDegree_eq_one hsource hh0 hHsq
  have hdegpos : 0 < h0.degree := by
    have hnd : 0 < h0.natDegree := by
      rw [hdegree]
      exact Nat.succ_pos 0
    simpa [Polynomial.degree_eq_natDegree hh0] using
      (Polynomial.natDegree_pos_iff_degree_pos (p := h0)).mp hnd
  obtain ⟨a, hroot⟩ := IsAlgClosed.exists_root h0 (ne_of_gt hdegpos)
  rcases hsource with
    ⟨_hHne, _hHdegree, hPdegree, hQdegree, hp8, hq10, hKeller⟩
  have hp : p.natDegree = 8 := by
    simpa only [p, natDegree_bivariate_eq_degreeOf_y] using hPdegree
  have hq : q.natDegree = 10 := by
    simpa only [q, natDegree_bivariate_eq_degreeOf_y] using hQdegree
  have hp8' : p.coeff 8 = H ^ 4 := by simpa only [p] using hp8
  have hq10' : q.coeff 10 = H ^ 5 := by simpa only [q] using hq10
  have hN' : (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0 := by
    simpa only [p, q] using haligned
  have hN0 :
      (5 : K[X]) * p.coeff 7 * h0 ^ 2 - (4 : K[X]) * q.coeff 9 = 0 := by
    simpa [hHsq] using hN'
  obtain ⟨j, hj, hjac⟩ := bivariateJacobian_eq_C_of_keller hKeller
  have hD : GCD369SourceXDeriv p * derivative q -
      derivative p * GCD369SourceXDeriv q =
        Polynomial.C (Polynomial.C j) := by
    simpa only [bivariateJacobian, xderiv, GCD369SourceXDeriv] using hjac
  let rho : RatFunc K :=
    RatFunc.C (degreeZeroClearedIntegerScale810 : K) *
      alignedSquareSourcePrimitive810
        (algebraMap K[X] (RatFunc K) h0)
        (algebraMap K[X] (RatFunc K) (p.coeff 7))
        (algebraMap K[X] (RatFunc K) (p.coeff 6))
        (algebraMap K[X] (RatFunc K) (p.coeff 5))
        (algebraMap K[X] (RatFunc K) (p.coeff 4))
        (algebraMap K[X] (RatFunc K) (p.coeff 3))
        (algebraMap K[X] (RatFunc K) (p.coeff 2))
        (algebraMap K[X] (RatFunc K) (p.coeff 1))
        (algebraMap K[X] (RatFunc K) (p.coeff 0))
        (algebraMap K[X] (RatFunc K) (q.coeff 9))
        (algebraMap K[X] (RatFunc K) (q.coeff 8))
        (algebraMap K[X] (RatFunc K) (q.coeff 7))
        (algebraMap K[X] (RatFunc K) (q.coeff 6))
        (algebraMap K[X] (RatFunc K) (q.coeff 5))
        (algebraMap K[X] (RatFunc K) (q.coeff 4))
        (algebraMap K[X] (RatFunc K) (q.coeff 3))
        (algebraMap K[X] (RatFunc K) (q.coeff 2))
        (algebraMap K[X] (RatFunc K) (q.coeff 1))
  have hpow : alignedSquareSourceClearingPower810 =
      alignedSquareRemainingPole810 := by
    rw [alignedSquareRemainingPole810_eq_sub, alignedSquareBaseOrder810_eq,
      Nat.sub_zero]
  have hclear :
      algebraMap K[X] (RatFunc K)
          (alignedSquareClearedNumerator810 h0 (p.coeff 7) (p.coeff 6)
            (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
            (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
            (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1)) =
        (algebraMap K[X] (RatFunc K) h0) ^
            alignedSquareRemainingPole810 * rho := by
    rw [← hpow]
    dsimp only [rho]
    exact alignedSquareClearedNumerator810_algebraMap_eq_pow_scaledPrimitive
      h0 (p.coeff 7) (p.coeff 6) (p.coeff 5) (p.coeff 4) (p.coeff 3)
      (p.coeff 2) (p.coeff 1) (p.coeff 0) (q.coeff 9) (q.coeff 8)
      (q.coeff 7) (q.coeff 6) (q.coeff 5) (q.coeff 4) (q.coeff 3)
      (q.coeff 2) (q.coeff 1) hh0 hN0
  have hnum : (degreeZeroClearedIntegerScale810 : RatFunc K) =
      RatFunc.C (degreeZeroClearedIntegerScale810 : K) :=
    (map_natCast (RatFunc.C : K →+* RatFunc K)
      degreeZeroClearedIntegerScale810).symm
  have hderiv :
      Differential.deriv rho =
        RatFunc.C ((degreeZeroClearedIntegerScale810 : K) * j) /
          algebraMap K[X] (RatFunc K) h0 := by
    dsimp only [rho]
    rw [← hnum]
    exact alignedSquarePrimitive810_scaledDeriv_eq_simplePole_of_source
      p q H h0 j hp hq hh0 hHsq hp8' hq10' hN' hD
  have hscale_ne : (degreeZeroClearedIntegerScale810 : K) ≠ 0 := by
    rw [degreeZeroClearedIntegerScale810_eq]
    norm_num
  have hjscaled : (degreeZeroClearedIntegerScale810 : K) * j ≠ 0 :=
    mul_ne_zero hscale_ne hj
  exact alignedSquareFace810_order119Ceiling h0 (p.coeff 7) (p.coeff 6)
    (p.coeff 5) (p.coeff 4) (p.coeff 3) (p.coeff 2) (p.coeff 1)
    (p.coeff 0) (q.coeff 8) (q.coeff 7) (q.coeff 6) (q.coeff 5)
    (q.coeff 4) (q.coeff 3) (q.coeff 2) (q.coeff 1) rho
    ((degreeZeroClearedIntegerScale810 : K) * j) a hh0 hdegree hroot
    hclear hderiv hjscaled

/-- Source-facing exclusion of a normalized scale-two `(8,10)` aligned
square face.  The nonsquare chamber is not reopened. -/
theorem normalized810ScaleTwo_alignedSquare_false
    {P Q : MvPolynomial (Fin 2) K} {H h0 : K[X]}
    (hsource : Normalized810LeadingCoreSource P Q H 2)
    (hh0 : h0 ≠ 0) (hHsq : H = h0 ^ 2)
    (haligned :
      let p := (Polynomial.Bivariate.equivMvPolynomial K).symm P
      let q := (Polynomial.Bivariate.equivMvPolynomial K).symm Q
      (5 : K[X]) * p.coeff 7 * H - (4 : K[X]) * q.coeff 9 = 0) :
    False :=
  alignedSquareFace810_squareChamber hsource hh0 hHsq haligned

/-- **CLOSED.** The remaining aligned-square exclusion of the normalized
`(8,10)` route. -/
theorem planeKeller810AlignedSquareExclusion_closed :
    PlaneKeller810AlignedSquareExclusion (K := K) :=
  fun _P _Q _H _h0 hsource hh0 hHsq hN =>
    normalized810ScaleTwo_alignedSquare_false hsource hh0 hHsq hN

end AlignedSquareChamber810

#print axioms alignedSquareFace810_squareChamber
#print axioms normalized810ScaleTwo_alignedSquare_false
#print axioms planeKeller810AlignedSquareExclusion_closed

end Max11DegreeRoutes
