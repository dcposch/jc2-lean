import Grok810ScaleZeroQuarticChamberUnownedTrees2Part0Row101Scratch
import Grok810ScaleZeroQuarticChamberUnownedTrees2Part0Row3Scratch

/-! # Unowned plan trees, `(8,10)` scale zero

9 chambers that need a nested case split whose leaves include a
load kill (a load column alone on top forces `p = 0`) or a tied-load
top-coefficient system.  Every pivot orientation, every face and every
load-column verdict is re-derived here with the exact Farkas engine;
the cofactors are the plan's, rescaled to these rows and re-checked.
10 scalar certificates.  Untracked working note.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

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

variable {k : Type*} [Field k] [CharZero k]

section QuarticChamberUnownedTrees2810

open private quarticChamberBCFG7810_impossible_row2 from Grok810ScaleZeroQuarticChamberUnownedTrees2Part0Row101Scratch in
open private quarticChamberBCFG7810_impossible_row3 from Grok810ScaleZeroQuarticChamberUnownedTrees2Part0Row3Scratch in
open private quarticChamberBCFG7810_impossible_row4 from Grok810ScaleZeroQuarticChamberUnownedTrees2Part0Row101Scratch in
set_option maxHeartbeats 64000000 in
/-- Tree branch 1 of `quarticChamberBCFG7810_impossible`. -/
private theorem quarticChamberBCFG7810_impossible_row1
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticChamberBCFG7810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hprim : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 1)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmuDeg : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxiDeg : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpiDeg : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpv0 : B.natDegree + C.natDegree < 3 * A.natDegree)
    (hpv1 : B.natDegree + C.natDegree < 3 * A.natDegree) :
    False := by
  obtain ⟨hA, hBne, hCne, hDz, hEz, hFne, hGne, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8, hq9⟩ := id hch
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hEn : E.natDegree = 0 := by simp [hEz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hFc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  rcases lt_trichotomy (B.natDegree) (0) with hpv2 | hpv2 | hpv2
  · exact quarticChamberBCFG7810_impossible_row2 l beta gamma delta epsilon zeta eta theta A B C D E F G hch hnc hkap hprim homi hnu hmuDeg hxiDeg hpiDeg hpv0 hpv1 hpv2
  · exact quarticChamberBCFG7810_impossible_row3 l beta gamma delta epsilon zeta eta theta A B C D E F G hch hnc hkap hprim homi hnu hmuDeg hxiDeg hpiDeg hpv0 hpv1 hpv2
  · exact quarticChamberBCFG7810_impossible_row4 l beta gamma delta epsilon zeta eta theta A B C D E F G hch hnc hkap hprim homi hnu hmuDeg hxiDeg hpiDeg hpv0 hpv1 hpv2

end QuarticChamberUnownedTrees2810

end Max11DegreeRoutes
