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
theorem xiQuarticChamberFace21810_coeff_top_S25
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * C.natDegree + E.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree)
    (ht2 : E.natDegree + G.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree) :
    (xiQuarticChamberFace21810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + C.natDegree + D.natDegree) =
      xiQuarticPowerInnerS25810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace21810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B * C * D)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc0 : ((A * B * C * D)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * E)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * E)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((E * G)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc2 : ((E * G)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  simp only [xiQuarticPowerInnerS25810]
  ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
