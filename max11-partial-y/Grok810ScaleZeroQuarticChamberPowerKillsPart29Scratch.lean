import Grok810ScaleZeroQuarticChamberFacesPart1Scratch
import Grok810ScaleZeroQuarticPowerCertificatesScratch

/-! # Power-target chamber kills, `(8,10)` scale zero

42 top-coefficient bridges and 59 chamber kills against the
tracked, green `Grok810ScaleZeroQuarticPowerCertificatesScratch`
(SHA 102939dc): each carrier's face top coefficient is extracted, and
the Singular-lifted isobaric identity then forces a product of non-zero
leading coefficients to vanish.  Which chambers qualify is decided by
`scripts/derive_810_quartic_chamber_killplan5.py`.  Untracked note.
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

section QuarticChamberPowerKills810

/-! ## Top-coefficient bridges to the power-target inner scalars -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace18810_coeff_top_S15
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (ht1 : 3 * C.natDegree = A.natDegree + 2 * D.natDegree)
    (ht2 : 2 * E.natDegree = A.natDegree + 2 * D.natDegree) :
    (muQuarticChamberFace18810 A B C D E F G).coeff
        (A.natDegree + 2 * D.natDegree) =
      muQuarticPowerInnerS15810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [muQuarticChamberFace18810, coeff_add, coeff_sub,
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
  have hd2 : (E ^ 2).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (E ^ 2).coeff (A.natDegree + 2 * D.natDegree) = E.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    all_goals simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  all_goals simp only [muQuarticPowerInnerS15810]
  all_goals ring


end QuarticChamberPowerKills810

end Max11DegreeRoutes
