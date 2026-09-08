import Grok810ScaleZeroQuarticChamberFacesPart1Scratch

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
theorem xiQuarticChamberFace1810_natDegree
    (A B C D E F G : k[X])
    (hCne : C ≠ 0)
    (hDne : D ≠ 0) :
    (xiQuarticChamberFace1810 A B C D E F G).natDegree =
      C.natDegree + 2 * D.natDegree := by
  have hc : (-(15 / 128 : k)) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace1810]
  rw [natDegree_smul _ hc, natDegree_mul hCne (pow_ne_zero 2 hDne)]
  simp only [natDegree_pow]
  all_goals omega

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
