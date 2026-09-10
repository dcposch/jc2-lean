import Grok810ScaleZeroQuarticChamberFacesPart1Scratch
import Grok810ScaleZeroQuarticPowerCertificatesScratch

/-! # Refined-leaf kills, `(8,10)` scale zero

22 of the 59 leaves of the 11 carrier-refined cells: 8 on a
single-monomial face of some carrier, 17 on the power systems
`S24`-`S34` that `Grok810ScaleZeroQuarticPowerCertificatesScratch`
produced for exactly those cells.  The leaves come from the tournament
of `…ChamberRefineScratch`; their load columns are decided against the
leaf's *full* conjunct set (cell + refinement) in
`scripts/derive_810_quartic_chamber_killplan6.py`.  Untracked note.
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

section QuarticChamberRefinedKills810

/-! ## Top-coefficient bridges for the refined leaves -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace15810_coeff_top_S28
    {A B C D E F G : k[X]}
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + G.natDegree = B.natDegree + 2 * C.natDegree)
    (ht2 : D.natDegree + E.natDegree = B.natDegree + 2 * C.natDegree) :
    (kappaQuarticChamberFace15810 A B C D E F G).coeff
        (B.natDegree + 2 * C.natDegree) =
      kappaQuarticPowerInnerS28810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace15810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((B * C ^ 2)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((B * C ^ 2)).coeff (B.natDegree + 2 * C.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * G)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc1 : ((B * G)).coeff (B.natDegree + 2 * C.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((D * E)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hDne hEne]
    all_goals omega
  have hc2 : ((D * E)).coeff (B.natDegree + 2 * C.natDegree) = D.leadingCoeff * E.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [kappaQuarticPowerInnerS28810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
