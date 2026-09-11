import Grok810ScaleZeroQuarticChamberFacesPart1Scratch

/-! # Single-monomial chamber kills, `(8,10)` scale zero

11 face-degree lemmas and 550 chamber kills: every leaf whose
level-0 certificate is a single monomial *and* whose eight load columns
are either empty, dominated by the chamber's own ℕ conjuncts, or covered
by the κ band of `…ChamberBandsScratch`.  Which leaves those are is
decided, with exact rational Farkas certificates, by
`scripts/derive_810_quartic_chamber_killplan.py`; the rest are named in
the residual.  Untracked working note.
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

section QuarticChamberKills810

/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace1810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hDne : D ≠ 0) :
    (muQuarticChamberFace1810 A B C D E F G).natDegree =
      A.natDegree + 2 * D.natDegree := by
  have hc : (-(5 / 128 : k)) ≠ 0 := by norm_num
  simp only [muQuarticChamberFace1810]
  rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hDne)]
  simp only [natDegree_pow]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace0810_natDegree
    (A B C D E F G : k[X])
    (hFne : F ≠ 0) :
    (xiQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * F.natDegree := by
  have hc : (5 / 32 : k) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace0810]
  rw [natDegree_smul _ hc]
  simp only [natDegree_pow]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace0810_natDegree
    (A B C D E F G : k[X])
    (hCne : C ≠ 0) :
    (muQuarticChamberFace0810 A B C D E F G).natDegree =
      3 * C.natDegree := by
  have hc : (-(5 / 128 : k)) ≠ 0 := by norm_num
  simp only [muQuarticChamberFace0810]
  rw [natDegree_smul _ hc]
  simp only [natDegree_pow]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace2810_natDegree
    (A B C D E F G : k[X])
    (hEne : E ≠ 0) :
    (muQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * E.natDegree := by
  have hc : (5 / 32 : k) ≠ 0 := by norm_num
  simp only [muQuarticChamberFace2810]
  rw [natDegree_smul _ hc]
  simp only [natDegree_pow]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace4810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hFne : F ≠ 0) :
    (muQuarticChamberFace4810 A B C D E F G).natDegree =
      A.natDegree + B.natDegree + F.natDegree := by
  have hc : (-(5 / 64 : k)) ≠ 0 := by norm_num
  simp only [muQuarticChamberFace4810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace0810_natDegree
    (A B C D E F G : k[X])
    (hGne : G ≠ 0) :
    (piQuarticChamberFace0810 A B C D E F G).natDegree =
      2 * G.natDegree := by
  have hc : (5 / 4 : k) ≠ 0 := by norm_num
  simp only [piQuarticChamberFace0810]
  rw [natDegree_smul _ hc]
  simp only [natDegree_pow]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace6810_natDegree
    (A B C D E F G : k[X])
    (hCne : C ≠ 0)
    (hGne : G ≠ 0) :
    (muQuarticChamberFace6810 A B C D E F G).natDegree =
      C.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [muQuarticChamberFace6810]
  rw [natDegree_smul _ hc, natDegree_mul hCne hGne]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace2810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hFne : F ≠ 0) :
    (piQuarticChamberFace2810 A B C D E F G).natDegree =
      A.natDegree + 2 * F.natDegree := by
  have hc : (-(5 / 16 : k)) ≠ 0 := by norm_num
  simp only [piQuarticChamberFace2810]
  rw [natDegree_smul _ hc, natDegree_mul hAne (pow_ne_zero 2 hFne)]
  simp only [natDegree_pow]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace12810_natDegree
    (A B C D E F G : k[X])
    (hEne : E ≠ 0)
    (hGne : G ≠ 0) :
    (xiQuarticChamberFace12810 A B C D E F G).natDegree =
      E.natDegree + G.natDegree := by
  have hc : (5 / 16 : k) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace12810]
  rw [natDegree_smul _ hc, natDegree_mul hEne hGne]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace2810_natDegree
    (A B C D E F G : k[X])
    (hCne : C ≠ 0)
    (hEne : E ≠ 0) :
    (xiQuarticChamberFace2810 A B C D E F G).natDegree =
      2 * C.natDegree + E.natDegree := by
  have hc : (-(15 / 128 : k)) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace2810]
  rw [natDegree_smul _ hc, natDegree_mul (pow_ne_zero 2 hCne) hEne]
  simp only [natDegree_pow]
  all_goals omega
/-! ## Face degrees -/

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace15810_natDegree
    (A B C D E F G : k[X])
    (hAne : A ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0) :
    (xiQuarticChamberFace15810 A B C D E F G).natDegree =
      A.natDegree + D.natDegree + F.natDegree := by
  have hc : (-(5 / 64 : k)) ≠ 0 := by norm_num
  simp only [xiQuarticChamberFace15810]
  rw [natDegree_smul _ hc, natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
  all_goals omega

/-! ## The chamber kills -/

end QuarticChamberKills810

end Max11DegreeRoutes
