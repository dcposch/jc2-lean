import Grok810ScaleZeroQuarticChamberFacesPart101Scratch
import Grok810ScaleZeroQuarticPowerCertificatesScratch
import Grok810ScaleZeroQuarticChamberCostLadderScratch
import Grok810ScaleZeroQuarticChamberRests2Scratch
import Grok810ScaleZeroQuarticChamberKills2Part101Scratch
import Grok810ScaleZeroQuarticChamberRefineScratch
import Grok810ScaleZeroQuarticChamberBandsScratch
import Grok810ScaleZeroQuarticChamberRests6Scratch

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
theorem kappaQuarticChamberFace15810_coeff_top_S25
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
      kappaQuarticPowerInnerS25810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
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
  all_goals simp only [kappaQuarticPowerInnerS25810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem muQuarticChamberFace19810_coeff_top_S25
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * C.natDegree = A.natDegree + 2 * D.natDegree)
    (ht2 : C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree) :
    (muQuarticChamberFace19810 A B C D E F G).coeff
        (A.natDegree + 2 * D.natDegree) =
      muQuarticPowerInnerS25810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace19810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * G)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc2 : ((C * G)).coeff (A.natDegree + 2 * D.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [muQuarticPowerInnerS25810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * E)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * E)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((E * G)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc2 : ((E * G)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [xiQuarticPowerInnerS25810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem piQuarticChamberFace13810_coeff_top_S25
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 4 * C.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree)
    (ht2 : 2 * C.natDegree + G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree)
    (ht3 : 2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree) :
    (piQuarticChamberFace13810 A B C D E F G).coeff
        (A.natDegree + C.natDegree + 2 * D.natDegree) =
      piQuarticPowerInnerS25810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace13810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * C * D ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * C * D ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 4).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 4).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C ^ 2 * G)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((C ^ 2 * G)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (G ^ 2).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (G ^ 2).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  all_goals simp only [piQuarticPowerInnerS25810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem xiQuarticChamberFace11810_coeff_top_S28
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : E.natDegree + G.natDegree = 2 * C.natDegree + E.natDegree) :
    (xiQuarticChamberFace11810 A B C D E F G).coeff
        (2 * C.natDegree + E.natDegree) =
      xiQuarticPowerInnerS28810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace11810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((C ^ 2 * E)).natDegree = 2 * C.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((C ^ 2 * E)).coeff (2 * C.natDegree + E.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((E * G)).natDegree = 2 * C.natDegree + E.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc1 : ((E * G)).coeff (2 * C.natDegree + E.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS28810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem kappaQuarticChamberFace11810_coeff_top_S29
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree)
    (ht2 : B.natDegree + G.natDegree = A.natDegree + 3 * B.natDegree)
    (ht3 : C.natDegree + F.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace11810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticPowerInnerS29810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace11810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc2 : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((C * F)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc3 : ((C * F)).coeff (A.natDegree + 3 * B.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  all_goals simp only [kappaQuarticPowerInnerS29810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem muQuarticChamberFace16810_coeff_top_S29
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + B.natDegree + F.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht2 : 3 * C.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht3 : C.natDegree + G.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree) :
    (muQuarticChamberFace16810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      muQuarticPowerInnerS29810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace16810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((C * G)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc3 : ((C * G)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  all_goals simp only [muQuarticPowerInnerS29810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem xiQuarticChamberFace14810_coeff_top_S29
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + D.natDegree + F.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree) :
    (xiQuarticChamberFace14810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + C.natDegree + D.natDegree) =
      xiQuarticPowerInnerS29810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace14810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B * C * D)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc0 : ((A * B * C * D)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * D * F)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    all_goals omega
  have hc1 : ((A * D * F)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS29810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem piQuarticChamberFace9810_coeff_top_S29
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : A.natDegree + 2 * B.natDegree + G.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht4 : 4 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht5 : A.natDegree + 2 * F.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht6 : 2 * C.natDegree + G.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht7 : 2 * G.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace9810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      piQuarticPowerInnerS29810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace9810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B ^ 2 * C ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B ^ 2 * C ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A * B * C * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc3 : ((A * B * C * F)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd4, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : ((A * F ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc5 : ((A * F ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd6 : ((C ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc6 : ((C ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd6, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd7 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc7 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd7, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
  all_goals simp only [piQuarticPowerInnerS29810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem kappaQuarticChamberFace17810_coeff_top_S30
    {A B C D E F G : k[X]}
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + G.natDegree = B.natDegree + 2 * C.natDegree)
    (ht2 : C.natDegree + F.natDegree = B.natDegree + 2 * C.natDegree) :
    (kappaQuarticChamberFace17810 A B C D E F G).coeff
        (B.natDegree + 2 * C.natDegree) =
      kappaQuarticPowerInnerS30810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace17810, coeff_add, coeff_sub,
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
  have hd2 : ((C * F)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc2 : ((C * F)).coeff (B.natDegree + 2 * C.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [kappaQuarticPowerInnerS30810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem muQuarticChamberFace19810_coeff_top_S30
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * C.natDegree = A.natDegree + 2 * D.natDegree)
    (ht2 : C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree) :
    (muQuarticChamberFace19810 A B C D E F G).coeff
        (A.natDegree + 2 * D.natDegree) =
      muQuarticPowerInnerS30810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace19810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * G)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc2 : ((C * G)).coeff (A.natDegree + 2 * D.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [muQuarticPowerInnerS30810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem xiQuarticChamberFace14810_coeff_top_S30
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + D.natDegree + F.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree) :
    (xiQuarticChamberFace14810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + C.natDegree + D.natDegree) =
      xiQuarticPowerInnerS30810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace14810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B * C * D)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc0 : ((A * B * C * D)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * D * F)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    all_goals omega
  have hc1 : ((A * D * F)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS30810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem piQuarticChamberFace13810_coeff_top_S30
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 4 * C.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree)
    (ht2 : 2 * C.natDegree + G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree)
    (ht3 : 2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree) :
    (piQuarticChamberFace13810 A B C D E F G).coeff
        (A.natDegree + C.natDegree + 2 * D.natDegree) =
      piQuarticPowerInnerS30810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace13810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * C * D ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * C * D ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 4).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 4).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C ^ 2 * G)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((C ^ 2 * G)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (G ^ 2).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (G ^ 2).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  all_goals simp only [piQuarticPowerInnerS30810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem kappaQuarticChamberFace11810_coeff_top_S32
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree)
    (ht2 : B.natDegree + G.natDegree = A.natDegree + 3 * B.natDegree)
    (ht3 : C.natDegree + F.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace11810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      kappaQuarticPowerInnerS32810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace11810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc2 : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((C * F)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc3 : ((C * F)).coeff (A.natDegree + 3 * B.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  all_goals simp only [kappaQuarticPowerInnerS32810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem muQuarticChamberFace16810_coeff_top_S32
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + B.natDegree + F.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht2 : 3 * C.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht3 : C.natDegree + G.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree) :
    (muQuarticChamberFace16810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      muQuarticPowerInnerS32810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace16810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((C * G)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc3 : ((C * G)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  all_goals simp only [muQuarticPowerInnerS32810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem xiQuarticChamberFace16810_coeff_top_S32
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * C.natDegree + E.natDegree = A.natDegree + 2 * B.natDegree + E.natDegree)
    (ht2 : E.natDegree + G.natDegree = A.natDegree + 2 * B.natDegree + E.natDegree) :
    (xiQuarticChamberFace16810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + E.natDegree) =
      xiQuarticPowerInnerS32810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace16810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * E)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * E)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((E * G)).natDegree = A.natDegree + 2 * B.natDegree + E.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc2 : ((E * G)).coeff (A.natDegree + 2 * B.natDegree + E.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [xiQuarticPowerInnerS32810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem piQuarticChamberFace9810_coeff_top_S32
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : A.natDegree + 2 * B.natDegree + G.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht3 : A.natDegree + B.natDegree + C.natDegree + F.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht4 : 4 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht5 : A.natDegree + 2 * F.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht6 : 2 * C.natDegree + G.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht7 : 2 * G.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace9810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      piQuarticPowerInnerS32810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace9810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B ^ 2 * C ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B ^ 2 * C ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A * B * C * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc3 : ((A * B * C * F)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd4, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : ((A * F ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc5 : ((A * F ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd6 : ((C ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc6 : ((C ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd6, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd7 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc7 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd7, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
  all_goals simp only [piQuarticPowerInnerS32810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem kappaQuarticChamberFace17810_coeff_top_S33
    {A B C D E F G : k[X]}
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + G.natDegree = B.natDegree + 2 * C.natDegree)
    (ht2 : C.natDegree + F.natDegree = B.natDegree + 2 * C.natDegree) :
    (kappaQuarticChamberFace17810 A B C D E F G).coeff
        (B.natDegree + 2 * C.natDegree) =
      kappaQuarticPowerInnerS33810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace17810, coeff_add, coeff_sub,
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
  have hd2 : ((C * F)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc2 : ((C * F)).coeff (B.natDegree + 2 * C.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [kappaQuarticPowerInnerS33810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem xiQuarticChamberFace11810_coeff_top_S33
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : E.natDegree + G.natDegree = 2 * C.natDegree + E.natDegree) :
    (xiQuarticChamberFace11810 A B C D E F G).coeff
        (2 * C.natDegree + E.natDegree) =
      xiQuarticPowerInnerS33810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace11810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((C ^ 2 * E)).natDegree = 2 * C.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((C ^ 2 * E)).coeff (2 * C.natDegree + E.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((E * G)).natDegree = 2 * C.natDegree + E.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc1 : ((E * G)).coeff (2 * C.natDegree + E.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [xiQuarticPowerInnerS33810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem kappaQuarticChamberFace14810_coeff_top_S34
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : D.natDegree + E.natDegree = C.natDegree + F.natDegree) :
    (kappaQuarticChamberFace14810 A B C D E F G).coeff
        (C.natDegree + F.natDegree) =
      kappaQuarticPowerInnerS34810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [kappaQuarticChamberFace14810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((C * F)).natDegree = C.natDegree + F.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc0 : ((C * F)).coeff (C.natDegree + F.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((D * E)).natDegree = C.natDegree + F.natDegree := by
    rw [natDegree_mul hDne hEne]
    all_goals omega
  have hc1 : ((D * E)).coeff (C.natDegree + F.natDegree) = D.leadingCoeff * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  all_goals simp only [kappaQuarticPowerInnerS34810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem muQuarticChamberFace19810_coeff_top_S34
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * C.natDegree = A.natDegree + 2 * D.natDegree)
    (ht2 : C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree) :
    (muQuarticChamberFace19810 A B C D E F G).coeff
        (A.natDegree + 2 * D.natDegree) =
      muQuarticPowerInnerS34810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace19810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * G)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc2 : ((C * G)).coeff (A.natDegree + 2 * D.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [muQuarticPowerInnerS34810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem xiQuarticChamberFace23810_coeff_top_S34
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * C.natDegree + E.natDegree = A.natDegree + D.natDegree + F.natDegree)
    (ht2 : E.natDegree + G.natDegree = A.natDegree + D.natDegree + F.natDegree) :
    (xiQuarticChamberFace23810 A B C D E F G).coeff
        (A.natDegree + D.natDegree + F.natDegree) =
      xiQuarticPowerInnerS34810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [xiQuarticChamberFace23810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D * F)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    all_goals omega
  have hc0 : ((A * D * F)).coeff (A.natDegree + D.natDegree + F.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * E)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * E)).coeff (A.natDegree + D.natDegree + F.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((E * G)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc2 : ((E * G)).coeff (A.natDegree + D.natDegree + F.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [xiQuarticPowerInnerS34810]
  all_goals ring

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
theorem piQuarticChamberFace13810_coeff_top_S34
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 4 * C.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree)
    (ht2 : 2 * C.natDegree + G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree)
    (ht3 : 2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree) :
    (piQuarticChamberFace13810 A B C D E F G).coeff
        (A.natDegree + C.natDegree + 2 * D.natDegree) =
      piQuarticPowerInnerS34810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace13810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * C * D ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * C * D ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 4).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 4).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd1, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C ^ 2 * G)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((C ^ 2 * G)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (G ^ 2).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (G ^ 2).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  all_goals simp only [piQuarticPowerInnerS34810]
  all_goals ring

/-! ## The refined-leaf kills -/

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
/-- Refined leaf 2 of chamber `BCDEG` / `CG·EE·CCC` dies on the single-monomial `κ` face. -/
theorem quarticRefinedBCDEG36L2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEG36L2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq5 hcq6 hrf0 hApos hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hrf0; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hrf0; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq3 hrf0; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
  have hr0 : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by clear * - hcq0 hcq1 hcq3 hrf0; omega) (by clear * - hcq1 hcq3 hcq6 hrf0; omega) (by clear * - hcq1 hrf0; omega) (by clear * - hrf0; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hrf0; omega)) hz0delta (Or.inr (by clear * - hcq1 hcq3 hcq6 hrf0; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq3 hcq6 hrf0; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq3 hrf0; omega))
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hrf0 hrf1 hrf2 hrf3 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hkap; omega

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
/-- Refined leaf 2 of chamber `BCEFG` / `CG·EE·CCC` dies on the single-monomial `κ` face. -/
theorem quarticRefinedBCEFG54L2810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCEFG54L2810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2⟩ := hch
  obtain ⟨hA, hBne, hCne, hDz, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hDn : D.natDegree = 0 := by simp [hDz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hDn hcq0 hcq1 hcq2 hcq3 hcq5 hcq6 hrf0 hApos hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq4 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hAD hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq4 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq4 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hDn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq6 hrf0; omega)
  have hr0 : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hDz (by clear * - hcq1 hcq4 hrf0; omega) (by clear * - hcq1 hrf0; omega) (by clear * - hrf0; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hrf0; omega)) hz0delta hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hcq6 hrf0; omega)) (Or.inr (by clear * - hcq1 hcq4 hrf0; omega))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hrf0 hrf1 hrf2 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hApos hAB hAC hAD hAE hAF hAG hDn hdp0 hkap; omega

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
/-- Refined leaf 4 of chamber `BCDEFG` / `CG·EE·CCC` dies on the single-monomial `κ` face. -/
theorem quarticRefinedBCDEFG108L4810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG108L4810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < C.natDegree + F.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq9 hrf0 hrf1 hApos hcq10 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree ∧ 3 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + G.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + F.natDegree < C.natDegree + F.natDegree ∧ C.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ 2 * D.natDegree < C.natDegree + F.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree ∧ 2 * A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + 2 * B.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + E.natDegree < C.natDegree + F.natDegree ∧ B.natDegree + D.natDegree < C.natDegree + F.natDegree ∧ 2 * C.natDegree < C.natDegree + F.natDegree ∧ G.natDegree < C.natDegree + F.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree ∧ A.natDegree + C.natDegree < C.natDegree + F.natDegree ∧ 2 * B.natDegree < C.natDegree + F.natDegree ∧ E.natDegree < C.natDegree + F.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree ∧ C.natDegree < C.natDegree + F.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < C.natDegree + F.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq4 hrf0 hcq10; omega)
  have hr0 : (kappaQuarticChamberRest3810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < C.natDegree + F.natDegree :=
    kappaQuarticChamberRest3810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by clear * - hcq1 hcq4 hrf0; omega) (by clear * - hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega) (by clear * - hcq1 hrf0; omega) (by clear * - hrf0; omega) (by clear * - hrf1; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf0 hcq10; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf0 hrf1 hcq10; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq4 hrf0 hcq10; omega)) (Or.inr (by clear * - hcq1 hcq4 hrf0; omega))
  have hlead : (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree :=
    kappaQuarticChamberFace3810_natDegree A B C D E F G hCne hFne
  rw [degreeZeroKappaQuartic810_eq_face3_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hkap; omega

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
/-- Refined leaf 6 of chamber `BCDEFG` / `CG·EE·CCC` dies on the single-monomial `κ` face. -/
theorem quarticRefinedBCDEFG108L6810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEFG108L6810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFne, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16, hcq17, hcq18, hcq19, hcq20, hcq21, hcq22⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < D.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hcq0 hcq1 hcq2 hcq3 hcq8 hrf0 hrf1 hApos hcq10 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree ∧ 3 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + G.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + F.natDegree < D.natDegree + E.natDegree ∧ C.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ 2 * D.natDegree < D.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0 hcq10; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hrf1 hcq10; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + E.natDegree < D.natDegree + E.natDegree ∧ B.natDegree + D.natDegree < D.natDegree + E.natDegree ∧ 2 * C.natDegree < D.natDegree + E.natDegree ∧ G.natDegree < D.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0 hcq10; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hcq10; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree ∧ A.natDegree + C.natDegree < D.natDegree + E.natDegree ∧ 2 * B.natDegree < D.natDegree + E.natDegree ∧ E.natDegree < D.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq10; omega)
      · exact Or.inr (by clear * - h hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hcq10; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hcq10; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree ∧ C.natDegree < D.natDegree + E.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < D.natDegree + E.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0; omega)
      · exact Or.inr (by clear * - h hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0; omega)
      · exact Or.inr (by clear * - h hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf1 hcq10; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hcq10; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq5 hrf0 hcq10; omega)
  have hr0 : (kappaQuarticChamberRest4810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < D.natDegree + E.natDegree :=
    kappaQuarticChamberRest4810_natDegree_lt_of_live_BCDEFG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 (by clear * - hcq0 hcq1 hcq5 hrf0; omega) (by clear * - hcq1 hcq5 hrf0 hcq10; omega) (by clear * - hcq1 hrf0; omega) (by clear * - hrf0; omega) (by clear * - hrf1; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq5 hrf0 hrf1 hcq10; omega)) hz0delta (Or.inr (by clear * - hcq1 hcq5 hrf0 hcq10; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq5 hrf0 hcq10; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq5 hrf0; omega))
  have hlead : (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree :=
    kappaQuarticChamberFace4810_natDegree A B C D E F G hDne hEne
  rw [degreeZeroKappaQuartic810_eq_face4_add_rest,
    natDegree_add_eq_left_of_natDegree_lt (by rwa [hlead]), hlead]
    at hkap
  clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hcq17 hcq18 hcq19 hcq20 hcq21 hcq22 hApos hAB hAC hAD hAE hAF hAG hdp0 hkap; omega


end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
/-- Refined leaf 1 of chamber `BCDEG` / `CG·DD·CCC` dies on power system `S25`. -/
theorem quarticRefinedBCDEG30L1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEG30L1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7, hrf8, hrf9, hrf10, hrf11, hrf12, hrf13, hrf14, hrf15, hrf16, hrf17, hrf18, hrf19, hrf20, hrf21⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hkbl, hkbbeta, hkbdelta, hkbzeta⟩ :=
    quarticSigmaKappaCostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < B.natDegree + 2 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq3 hcq4 hrf0 hrf4 hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * D.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hrf4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3 hcq4 hrf0; omega)
      · exact Or.inr (by clear * - h hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hrf4; omega)
      · exact Or.inr (by clear * - h hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf4; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hrf4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq3 hcq4 hrf0; omega)
      · exact Or.inr (by clear * - h hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hrf4; omega)
      · exact Or.inr (by clear * - h hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf4; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hrf4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hrf4; omega)
      · exact Or.inr (by clear * - h hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf0 hrf4; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq1 hrf4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq3 hcq4; omega)
      · exact Or.inr (by clear * - h hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hrf4; omega)
      · exact Or.inr (by clear * - h hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
  have hr0 : (kappaQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest15810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by clear * - hcq2; omega) (by clear * - hcq2 hrf4; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf4; omega)) hz0delta (Or.inr (by clear * - hcq2 hrf4; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf4; omega)) (Or.inr (by clear * - hcq2; omega))
  have hct0 := kappaQuarticChamberFace15810_coeff_top_S25 hBne hCne hDne hEne hGne (A := A) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega)
  have hqq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega
  rw [degreeZeroKappaQuartic810_eq_face15_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hqq0
  have hin0 : kappaQuarticPowerInnerS25810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hqq0
  have hdp1 : 0 < A.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq3 hcq4 hrf0 hrf4 hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + G.natDegree < A.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree < A.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree < A.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree < A.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
  have hr1 : (muQuarticChamberRest19810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + 2 * D.natDegree :=
    muQuarticChamberRest19810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hrf4; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hrf4; omega) (by clear * - hcq0 hcq1 hcq2 hrf4; omega) (by clear * - hcq0 hcq3; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf4; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf4; omega))
  have hct1 := muQuarticChamberFace19810_coeff_top_S25 hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega)
  have hqq1 : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hmu]
    clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega
  rw [degreeZeroMuQuartic810_eq_face19_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hqq1
  have hin1 : muQuarticPowerInnerS25810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hqq1
  have hdp2 : 0 < A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq3 hcq4 hrf0 hrf4 hzero; omega)
  have hz2l : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + G.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
  have hz2beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
  have hz2delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ 3 * B.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ B.natDegree + E.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree ∧ C.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree) := by
      rcases hkbdelta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hrf0 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
  have hr2 : (xiQuarticChamberRest21810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + B.natDegree + C.natDegree + D.natDegree :=
    xiQuarticChamberRest21810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp2 hFz (by clear * - hcq0 hcq1 hcq2 hrf4; omega) (by clear * - hcq0 hcq2 hcq3; omega) (by clear * - hcq0 hcq1 hcq2 hrf4; omega) (by clear * - hcq0 hcq1 hcq2 hrf4; omega) (by clear * - hcq0 hcq2 hrf4; omega) (by clear * - hcq0 hcq2 hcq3 hrf4; omega) (by clear * - hrf4; omega) hz2l hz2beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf0 hrf4; omega)) hz2delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf0 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf4; omega))
  have hct2 := xiQuarticChamberFace21810_coeff_top_S25 hAne hBne hCne hDne hEne hGne (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2; omega)
  have hqq2 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2; omega
  rw [degreeZeroXiQuartic810_eq_face21_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr2,
    add_zero] at hqq2
  have hin2 : xiQuarticPowerInnerS25810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct2.symm.trans hqq2
  have hdp3 : 0 < A.natDegree + C.natDegree + 2 * D.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq3 hcq4 hrf0 hrf4 hzero; omega)
  have hz3l : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 5 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 3 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + G.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ C.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf4; omega)
  have hz3beta : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 3 * B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf0 hrf4; omega)
  have hz3delta : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + 3 * B.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ 2 * B.natDegree + D.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ B.natDegree + 2 * C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree ∧ D.natDegree + E.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + B.natDegree + C.natDegree < A.natDegree + C.natDegree + 2 * D.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hrf4; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hrf4; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hrf4; omega)
  have hr3 : (piQuarticChamberRest13810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < A.natDegree + C.natDegree + 2 * D.natDegree :=
    piQuarticChamberRest13810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp3 hFz (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hrf4; omega) (by clear * - hcq0 hcq1 hcq2; omega) (by clear * - hcq0 hcq1 hcq2 hrf4; omega) (by clear * - hcq0 hcq2; omega) (by clear * - hcq0 hcq2 hcq3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hrf4; omega) (by clear * - hcq0 hcq1 hcq2 hrf4; omega) (by clear * - hcq0 hcq1 hcq2 hrf4; omega) (by clear * - hcq0 hcq2 hrf4; omega) (by clear * - hcq0 hcq3; omega) (by clear * - hcq0 hcq2 hcq3 hrf4; omega) hz3l hz3beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf4; omega)) hz3delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf4; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hrf4; omega))
  have hct3 := piQuarticChamberFace13810_coeff_top_S25 hAne hCne hDne hGne (B := B) (E := E) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2 hdp3; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2 hdp3; omega)
  have hqq3 : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hpi]
    clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hrf10 hrf11 hrf12 hrf13 hrf14 hrf15 hrf16 hrf17 hrf18 hrf19 hrf20 hrf21 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1 hdp2 hdp3; omega
  rw [degreeZeroPiQuartic810_eq_face13_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr3,
    add_zero] at hqq3
  have hin3 : piQuarticPowerInnerS25810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct3.symm.trans hqq3
  have hAc : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hAne
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS25810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hin2 hin3 hAc hBc hCc hDc hEc hGc

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
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
/-- Refined leaf 1 of chamber `BCDEG` / `CG·EE·CCC` dies on power system `S28`. -/
theorem quarticRefinedBCDEG36L1810_impossible
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hch : QuarticRefinedBCDEG36L1810 A B C D E F G)
    (hnc : ¬ (B.natDegree = 0 ∧ C.natDegree = 0 ∧ D.natDegree = 0 ∧
        E.natDegree = 0 ∧ F.natDegree = 0 ∧ G.natDegree = 0))
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G).natDegree = 0) :
    False := by
  obtain ⟨hcell, hrf0, hrf1, hrf2, hrf3, hrf4, hrf5, hrf6, hrf7, hrf8, hrf9⟩ := hch
  obtain ⟨hA, hBne, hCne, hDne, hEne, hFz, hGne, hcq0, hcq1, hcq2, hcq3, hcq4, hcq5, hcq6, hcq7, hcq8, hcq9, hcq10, hcq11, hcq12, hcq13, hcq14, hcq15, hcq16⟩ := hcell
  obtain ⟨hApos, hAB, hAC, hAD, hAE, hAF, hAG⟩ := id hA
  have hFn : F.natDegree = 0 := by simp [hFz]
  have hAne : A ≠ 0 := by
    intro h0
    have hz0 : A.natDegree = 0 := by simp [h0]
    clear * - hApos hz0; omega
  obtain ⟨hbl, hbbeta, hbdelta, hbzeta, hbtheta⟩ :=
    quarticSigma_kappaLoadBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hkap
  obtain ⟨hnbl, hnbbeta, hnbdelta, hnbzeta, hnbtheta⟩ :=
    quarticSigmaN2CostBands810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G hA hnu hkap
  have hdp0 : 0 < B.natDegree + 2 * C.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq6 hrf0 hApos hzero; omega)
  have hz0l : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 3 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + G.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * D.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbls : l = 0 ∨ (5 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbl with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq6; omega)
  have hz0beta : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + E.natDegree < B.natDegree + 2 * C.natDegree ∧ B.natDegree + D.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * C.natDegree < B.natDegree + 2 * C.natDegree ∧ G.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbbetas : beta = 0 ∨ (4 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbbeta with h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq6; omega)
  have hz0delta : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ A.natDegree + C.natDegree < B.natDegree + 2 * C.natDegree ∧ 2 * B.natDegree < B.natDegree + 2 * C.natDegree ∧ E.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbdeltas : delta = 0 ∨ (3 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbdelta with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hAF hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
  have hz0zeta : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree ∧ C.natDegree < B.natDegree + 2 * C.natDegree) := by
    have hbzetas : zeta = 0 ∨ (2 * A.natDegree < B.natDegree + 2 * C.natDegree) := by
      rcases hnbzeta with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq3 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hFn hcq0 hcq1 hcq5 hcq6 hrf0; omega)
      · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6; omega)
    rcases hbzetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq6; omega)
  have hr0 : (kappaQuarticChamberRest15810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < B.natDegree + 2 * C.natDegree :=
    kappaQuarticChamberRest15810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp0 hFz (by clear * - hcq2; omega) (by clear * - hcq0 hcq2 hcq3 hcq6; omega) hz0l hz0beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6; omega)) hz0delta (Or.inr (by clear * - hcq0 hcq2 hcq6 hrf0; omega)) hz0zeta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6; omega)) (Or.inr (by clear * - hcq2; omega))
  have hct0 := kappaQuarticChamberFace15810_coeff_top_S28 hBne hCne hDne hEne hGne (A := A) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega)
  have hqq0 : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hkap]
    clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0; omega
  rw [degreeZeroKappaQuartic810_eq_face15_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr0,
    add_zero] at hqq0
  have hin0 : kappaQuarticPowerInnerS28810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct0.symm.trans hqq0
  have hdp1 : 0 < 2 * C.natDegree + E.natDegree := by
    by_contra hzero
    exact hnc (by clear * - hFn hcq0 hcq1 hcq2 hcq6 hrf0 hApos hzero; omega)
  have hz1l : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + 2 * B.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + 2 * C.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + C.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + 2 * D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + G.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbls : l = 0 ∨ (4 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbl with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
    rcases hbls with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq3 hcq6 hrf0; omega)
  have hz1beta : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ 2 * B.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + 2 * C.natDegree < 2 * C.natDegree + E.natDegree ∧ D.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbbetas : beta = 0 ∨ (3 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbbeta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
    rcases hbbetas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6 hrf0; omega)
  have hz1delta : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree ∧ A.natDegree + B.natDegree + C.natDegree < 2 * C.natDegree + E.natDegree ∧ 3 * B.natDegree < 2 * C.natDegree + E.natDegree ∧ B.natDegree + E.natDegree < 2 * C.natDegree + E.natDegree ∧ C.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
    have hbdeltas : delta = 0 ∨ (2 * A.natDegree + D.natDegree < 2 * C.natDegree + E.natDegree) := by
      rcases hbdelta with h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (by clear * - h hcq0 hcq2 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
      · exact absurd h (by clear * - hFn hcq0 hcq1 hcq2 hcq6; omega)
      · exact Or.inr (by clear * - h hcq0 hcq3 hcq6; omega)
    rcases hbdeltas with h | h
    · exact Or.inl h
    · exact Or.inr (by clear * - h hcq0 hcq1 hcq2 hcq6 hrf0; omega)
  have hr1 : (xiQuarticChamberRest11810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).natDegree < 2 * C.natDegree + E.natDegree :=
    xiQuarticChamberRest11810_natDegree_lt_of_live_BCDEG l beta gamma delta epsilon zeta eta theta
      A B C D E F G hdp1 hFz (by clear * - hcq0 hcq1 hcq2 hcq6; omega) (by clear * - hcq2; omega) (by clear * - hcq0 hcq2 hcq3; omega) (by clear * - hcq0 hcq1 hcq2 hcq3 hcq6; omega) (by clear * - hcq0 hcq1 hcq2 hcq6; omega) (by clear * - hcq0 hcq2 hcq6; omega) (by clear * - hcq0 hcq2 hcq3 hcq6; omega) (by clear * - hcq0 hcq3 hcq6; omega) hz1l hz1beta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq6; omega)) hz1delta (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq6; omega)) (Or.inr (by clear * - hcq0 hcq1 hcq2 hcq3 hcq6; omega))
  have hct1 := xiQuarticChamberFace11810_coeff_top_S28 hCne hEne hGne (A := A) (B := B) (D := D) (F := F) (by clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega)
  have hqq1 : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
      A B C D E F G).coeff (2 * C.natDegree + E.natDegree) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [hxi]
    clear * - hrf0 hrf1 hrf2 hrf3 hrf4 hrf5 hrf6 hrf7 hrf8 hrf9 hcq0 hcq1 hcq2 hcq3 hcq4 hcq5 hcq6 hcq7 hcq8 hcq9 hcq10 hcq11 hcq12 hcq13 hcq14 hcq15 hcq16 hApos hAB hAC hAD hAE hAF hAG hFn hdp0 hdp1; omega
  rw [degreeZeroXiQuartic810_eq_face11_add_rest,
    coeff_add, coeff_eq_zero_of_natDegree_lt hr1,
    add_zero] at hqq1
  have hin1 : xiQuarticPowerInnerS28810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 :=
    hct1.symm.trans hqq1
  have hBc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  have hCc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  have hDc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  have hEc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  have hGc : G.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hGne
  exact quarticPowerInnerS28810_false A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff hin0 hin1 hBc hCc hDc hEc hGc

end QuarticChamberRefinedKills810

end Max11DegreeRoutes
