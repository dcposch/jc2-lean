import Grok810ScaleZeroQuarticChamberRests2Scratch

/-! # Cost-ladder chamber kills, `(8,10)` scale zero

265 further single-monomial chamber kills.  Untracked note.
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

section QuarticChamberKills2810

/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace0810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hBne : B ≠ 0) :
    (kappaQuarticChamberFace0810 A B C D E F G).natDegree =
      A.natDegree + 3 * B.natDegree := by
  have hc : (5 / 512 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace0810]
  rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 3 hBne)]
  simp only [natDegree_pow]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace2810_natDegree
    (A B C D E F G : k[X])
    (hBne : B ≠ 0)
    (hGne : G ≠ 0) :
    (kappaQuarticChamberFace2810 A B C D E F G).natDegree =
      B.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace2810]
  rw [natDegree_smul _ hc, natDegree_mul hBne hGne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace4810_natDegree
    (A B C D E F G : k[X])
    (hDne : D ≠ 0)
    (hEne : E ≠ 0) :
    (kappaQuarticChamberFace4810 A B C D E F G).natDegree =
      D.natDegree + E.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace4810]
  rw [natDegree_smul _ hc, natDegree_mul hDne hEne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace4810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0) :
    (xiQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
  have hc : (15 / 256 : k) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace4810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace5810_natDegree
    (A B C D E F G : k[X])
    (hBne : B ≠ 0)
    (hCne : C ≠ 0) :
    (kappaQuarticChamberFace5810 A B C D E F G).natDegree =
      B.natDegree + 2 * C.natDegree := by
  have hc : (-(15 / 128 : k)) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace5810]
  rw [natDegree_smul _ hc, natDegree_mul hBne (pow_ne_zero 2 hCne)]
  simp only [natDegree_pow]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace3810_natDegree
    (A B C D E F G : k[X])
    (hCne : C ≠ 0)
    (hFne : F ≠ 0) :
    (kappaQuarticChamberFace3810 A B C D E F G).natDegree =
      C.natDegree + F.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [kappaQuarticChamberFace3810]
  rw [natDegree_smul _ hc, natDegree_mul hCne hFne]
  all_goals omega
set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace10810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hEne : E ≠ 0) :
    (xiQuarticChamberFace10810 A B C D E F G).natDegree =
      A.natDegree + 2 * B.natDegree + E.natDegree := by
  have hc : (15 / 512 : k) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace10810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
  simp only [natDegree_pow]
  all_goals omega

/-! ## The chamber kills unblocked by the cost ladder -/

end QuarticChamberKills2810

end Max11DegreeRoutes
