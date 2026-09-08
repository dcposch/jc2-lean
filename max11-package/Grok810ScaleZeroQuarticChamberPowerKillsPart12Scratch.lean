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
theorem piQuarticChamberFace7810_coeff_top_S07
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht3 : A.natDegree + C.natDegree + 2 * D.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht4 : 4 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht5 : A.natDegree + 2 * F.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace7810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      piQuarticPowerInnerS07810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  simp only [piQuarticChamberFace7810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B ^ 2 * C ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) (pow_ne_zero 2 hCne), natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B ^ 2 * C ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * B * C * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc2 : ((A * B * C * F)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A * C * D ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((A * C * D ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : ((A * F ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc5 : ((A * F ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4, hc5]
  simp only [piQuarticPowerInnerS07810]
  ring


end QuarticChamberPowerKills810

end Max11DegreeRoutes
