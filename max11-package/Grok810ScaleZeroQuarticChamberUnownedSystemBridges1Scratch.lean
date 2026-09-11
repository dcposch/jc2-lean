import Grok810ScaleZeroQuarticChamberUnownedSystemPackets2Scratch
import Grok810ScaleZeroQuarticChamberUnownedSystemPackets1Scratch

/-! # `_coeff_top` bridges for the unowned systems, part 1/2

53 of the 62 top-coefficient bridges, one per (carrier,
face packet) the multi-carrier systems use.  Untracked working note.
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

section QuarticChamberUnownedSystemBridges1810

/-! ## Top-coefficient bridges -/

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace6000810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + G.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace6000810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      (5 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff := by
  simp only [kappaQuarticChamberFace6000810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc1 : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberFace6000810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + B.natDegree + G.natDegree = 2 * A.natDegree + 3 * B.natDegree) :
    (nuQuarticChamberFace6000810 A B C D E F G).coeff
        (2 * A.natDegree + 3 * B.natDegree) =
      (-5 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 + (-5 / 128 : k) * A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
  simp only [nuQuarticChamberFace6000810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hGne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * G)).coeff (2 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberFace6000810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * A.natDegree + B.natDegree + G.natDegree = 3 * A.natDegree + 3 * B.natDegree) :
    (omicronQuarticChamberFace6000810 A B C D E F G).coeff
        (3 * A.natDegree + 3 * B.natDegree) =
      (-5 / 65536 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
  simp only [omicronQuarticChamberFace6000810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 2 * B * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 2 * B * G)).coeff (3 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace6000810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + 2 * B.natDegree + G.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : 2 * G.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace6000810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      (15 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 + (5 / 64 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 := by
  simp only [piQuarticChamberFace6000810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 4)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 4 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 4)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberFace6000810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * A.natDegree + B.natDegree + G.natDegree = 4 * A.natDegree + 3 * B.natDegree) :
    (primitiveQuarticChamberFace6000810 A B C D E F G).coeff
        (4 * A.natDegree + 3 * B.natDegree) =
      (-5 / 65536 : k) * A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
  simp only [primitiveQuarticChamberFace6000810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 4 * B ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 4 * B ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 3 * B * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 3 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 3 * B * G)).coeff (4 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace6000810_coeff_top
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : C.natDegree + G.natDegree = 3 * C.natDegree) :
    (muQuarticChamberFace6000810 A B C D E F G).coeff
        (3 * C.natDegree) =
      (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff := by
  simp only [muQuarticChamberFace6000810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : (C ^ 3).natDegree = 3 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : (C ^ 3).coeff (3 * C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C * G)).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc1 : ((C * G)).coeff (3 * C.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace6001810_coeff_top
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * C.natDegree + G.natDegree = 4 * C.natDegree)
    (ht2 : 2 * G.natDegree = 4 * C.natDegree) :
    (piQuarticChamberFace6001810 A B C D E F G).coeff
        (4 * C.natDegree) =
      (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 := by
  simp only [piQuarticChamberFace6001810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : (C ^ 4).natDegree = 4 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : (C ^ 4).coeff (4 * C.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * G)).natDegree = 4 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * G)).coeff (4 * C.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (G ^ 2).natDegree = 4 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (G ^ 2).coeff (4 * C.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace6001810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree)
    (ht2 : C.natDegree + F.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace6001810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      (5 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 + (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * C.leadingCoeff * F.leadingCoeff := by
  simp only [kappaQuarticChamberFace6001810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * F)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc2 : ((C * F)).coeff (A.natDegree + 3 * B.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace6001810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + B.natDegree + F.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht2 : 3 * C.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree) :
    (muQuarticChamberFace6001810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (15 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff + (-5 / 64 : k) * A.leadingCoeff * B.leadingCoeff * F.leadingCoeff + (-5 / 128 : k) * C.leadingCoeff ^ 3 := by
  simp only [muQuarticChamberFace6001810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberFace6001810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + B.natDegree + 2 * C.natDegree = 2 * A.natDegree + 3 * B.natDegree)
    (ht2 : A.natDegree + C.natDegree + F.natDegree = 2 * A.natDegree + 3 * B.natDegree) :
    (nuQuarticChamberFace6001810 A B C D E F G).coeff
        (2 * A.natDegree + 3 * B.natDegree) =
      (-5 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 + (15 / 1024 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 128 : k) * A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
  simp only [nuQuarticChamberFace6001810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * C * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) hFne, natDegree_mul hAne hCne]
    all_goals omega
  have hc2 : ((A * C * F)).coeff (2 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberFace6001810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : 2 * A.natDegree + B.natDegree + 2 * C.natDegree = 3 * A.natDegree + 3 * B.natDegree)
    (ht2 : 2 * A.natDegree + C.natDegree + F.natDegree = 3 * A.natDegree + 3 * B.natDegree) :
    (omicronQuarticChamberFace6001810 A B C D E F G).coeff
        (3 * A.natDegree + 3 * B.natDegree) =
      (-5 / 65536 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 + (15 / 16384 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
  simp only [omicronQuarticChamberFace6001810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 2 * B * C ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 2 * B * C ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A ^ 2 * C * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A ^ 2 * C * F)).coeff (3 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace6002810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : A.natDegree + B.natDegree + C.natDegree + F.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht3 : 4 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht4 : A.natDegree + 2 * F.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace6002810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      (15 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 + (-45 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 + (5 / 32 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (-5 / 16 : k) * A.leadingCoeff * F.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 := by
  simp only [piQuarticChamberFace6002810, coeff_add, coeff_sub,
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
  have hd3 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((A * F ^ 2)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : ((A * F ^ 2)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4]
  ring

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberFace6001810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : 3 * A.natDegree + B.natDegree + 2 * C.natDegree = 4 * A.natDegree + 3 * B.natDegree)
    (ht2 : 3 * A.natDegree + C.natDegree + F.natDegree = 4 * A.natDegree + 3 * B.natDegree) :
    (primitiveQuarticChamberFace6001810 A B C D E F G).coeff
        (4 * A.natDegree + 3 * B.natDegree) =
      (-5 / 65536 : k) * A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 + (15 / 16384 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff := by
  simp only [primitiveQuarticChamberFace6001810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 4 * B ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 4 * B ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 3 * B * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 3 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 3 * B * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A ^ 3 * C * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 3 hAne) hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A ^ 3 * C * F)).coeff (4 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace6002810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree)
    (ht2 : B.natDegree + G.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace6002810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      (5 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 + (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff := by
  simp only [kappaQuarticChamberFace6002810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc2 : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace6002810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * C.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht2 : C.natDegree + G.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree) :
    (muQuarticChamberFace6002810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (15 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff := by
  simp only [muQuarticChamberFace6002810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * G)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc2 : ((C * G)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberFace6002810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + B.natDegree + 2 * C.natDegree = 2 * A.natDegree + 3 * B.natDegree)
    (ht2 : A.natDegree + B.natDegree + G.natDegree = 2 * A.natDegree + 3 * B.natDegree) :
    (nuQuarticChamberFace6002810 A B C D E F G).coeff
        (2 * A.natDegree + 3 * B.natDegree) =
      (-5 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 + (15 / 1024 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 128 : k) * A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
  simp only [nuQuarticChamberFace6002810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * B * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hGne, natDegree_mul hAne hBne]
    all_goals omega
  have hc2 : ((A * B * G)).coeff (2 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberFace6002810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * A.natDegree + B.natDegree + 2 * C.natDegree = 3 * A.natDegree + 3 * B.natDegree)
    (ht2 : 2 * A.natDegree + B.natDegree + G.natDegree = 3 * A.natDegree + 3 * B.natDegree) :
    (omicronQuarticChamberFace6002810 A B C D E F G).coeff
        (3 * A.natDegree + 3 * B.natDegree) =
      (-5 / 65536 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 + (15 / 16384 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
  simp only [omicronQuarticChamberFace6002810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 2 * B * C ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 2 * B * C ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A ^ 2 * B * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A ^ 2 * B * G)).coeff (3 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace6003810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + 2 * B.natDegree + 2 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht2 : A.natDegree + 2 * B.natDegree + G.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht3 : 4 * C.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht4 : 2 * C.natDegree + G.natDegree = 2 * A.natDegree + 4 * B.natDegree)
    (ht5 : 2 * G.natDegree = 2 * A.natDegree + 4 * B.natDegree) :
    (piQuarticChamberFace6003810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      (15 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 + (-45 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 + (5 / 64 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 := by
  simp only [piQuarticChamberFace6003810, coeff_add, coeff_sub,
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
  have hd2 : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (C ^ 4).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (C ^ 4).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((C ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : ((C ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc5 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd5, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4, hc5]
  ring

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberFace6002810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * A.natDegree + B.natDegree + 2 * C.natDegree = 4 * A.natDegree + 3 * B.natDegree)
    (ht2 : 3 * A.natDegree + B.natDegree + G.natDegree = 4 * A.natDegree + 3 * B.natDegree) :
    (primitiveQuarticChamberFace6002810 A B C D E F G).coeff
        (4 * A.natDegree + 3 * B.natDegree) =
      (-5 / 65536 : k) * A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 + (15 / 16384 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
  simp only [primitiveQuarticChamberFace6002810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 4 * B ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 4 * B ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 3 * B * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 3 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 3 * B * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A ^ 3 * B * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 3 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A ^ 3 * B * G)).coeff (4 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace6003810_coeff_top
    {A B C D E F G : k[X]}
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + G.natDegree = B.natDegree + 2 * C.natDegree) :
    (kappaQuarticChamberFace6003810 A B C D E F G).coeff
        (B.natDegree + 2 * C.natDegree) =
      (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff := by
  simp only [kappaQuarticChamberFace6003810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((B * C ^ 2)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((B * C ^ 2)).coeff (B.natDegree + 2 * C.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * G)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc1 : ((B * G)).coeff (B.natDegree + 2 * C.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberFace6003810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + B.natDegree + G.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree) :
    (nuQuarticChamberFace6003810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + 2 * C.natDegree) =
      (15 / 1024 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 128 : k) * A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
  simp only [nuQuarticChamberFace6003810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B * C ^ 2)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B * C ^ 2)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * G)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hGne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * G)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberFace6003810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * A.natDegree + B.natDegree + G.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree) :
    (omicronQuarticChamberFace6003810 A B C D E F G).coeff
        (2 * A.natDegree + B.natDegree + 2 * C.natDegree) =
      (15 / 16384 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
  simp only [omicronQuarticChamberFace6003810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B * C ^ 2)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B * C ^ 2)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 2 * B * G)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 2 * B * G)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberFace6003810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * A.natDegree + B.natDegree + G.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree) :
    (primitiveQuarticChamberFace6003810 A B C D E F G).coeff
        (3 * A.natDegree + B.natDegree + 2 * C.natDegree) =
      (15 / 16384 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
  simp only [primitiveQuarticChamberFace6003810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 3 * B * C ^ 2)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 3 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 3 * B * C ^ 2)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 3 * B * G)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 3 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 3 * B * G)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace6003810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * C.natDegree = A.natDegree + 2 * D.natDegree)
    (ht2 : C.natDegree + G.natDegree = A.natDegree + 2 * D.natDegree) :
    (muQuarticChamberFace6003810 A B C D E F G).coeff
        (A.natDegree + 2 * D.natDegree) =
      (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff ^ 2 + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff := by
  simp only [muQuarticChamberFace6003810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D ^ 2)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * D ^ 2)).coeff (A.natDegree + 2 * D.natDegree) = A.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 3).natDegree = A.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 3).coeff (A.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * G)).natDegree = A.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc2 : ((C * G)).coeff (A.natDegree + 2 * D.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace6004810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 4 * C.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree)
    (ht2 : 2 * C.natDegree + G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree)
    (ht3 : 2 * G.natDegree = A.natDegree + C.natDegree + 2 * D.natDegree) :
    (piQuarticChamberFace6004810 A B C D E F G).coeff
        (A.natDegree + C.natDegree + 2 * D.natDegree) =
      (5 / 32 : k) * A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 := by
  simp only [piQuarticChamberFace6004810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * C * D ^ 2)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) (pow_ne_zero 2 hDne), natDegree_mul hAne hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * C * D ^ 2)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = A.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (C ^ 4).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (C ^ 4).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C ^ 2 * G)).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((C ^ 2 * G)).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (G ^ 2).natDegree = A.natDegree + C.natDegree + 2 * D.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (G ^ 2).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberFace6000810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + D.natDegree + G.natDegree = A.natDegree + 2 * C.natDegree + D.natDegree) :
    (n3QuarticChamberFace6000810 A B C D E F G).coeff
        (A.natDegree + 2 * C.natDegree + D.natDegree) =
      (45 / 2048 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff + (-15 / 256 : k) * A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
  simp only [n3QuarticChamberFace6000810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * C ^ 2 * D)).natDegree = A.natDegree + 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * C ^ 2 * D)).coeff (A.natDegree + 2 * C.natDegree + D.natDegree) = A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * D * G)).natDegree = A.natDegree + 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hGne, natDegree_mul hAne hDne]
    all_goals omega
  have hc1 : ((A * D * G)).coeff (A.natDegree + 2 * C.natDegree + D.natDegree) = A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberFace6000810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * A.natDegree + D.natDegree + G.natDegree = 2 * A.natDegree + 2 * C.natDegree + D.natDegree) :
    (n4QuarticChamberFace6000810 A B C D E F G).coeff
        (2 * A.natDegree + 2 * C.natDegree + D.natDegree) =
      (-15 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff + (5 / 256 : k) * A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
  simp only [n4QuarticChamberFace6000810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * C ^ 2 * D)).natDegree = 2 * A.natDegree + 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * C ^ 2 * D)).coeff (2 * A.natDegree + 2 * C.natDegree + D.natDegree) = A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 2 * D * G)).natDegree = 2 * A.natDegree + 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 2 * D * G)).coeff (2 * A.natDegree + 2 * C.natDegree + D.natDegree) = A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace6004810_coeff_top
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : C.natDegree + G.natDegree = 3 * C.natDegree)
    (ht2 : 2 * E.natDegree = 3 * C.natDegree) :
    (muQuarticChamberFace6004810 A B C D E F G).coeff
        (3 * C.natDegree) =
      (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff + (5 / 32 : k) * E.leadingCoeff ^ 2 := by
  simp only [muQuarticChamberFace6004810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : (C ^ 3).natDegree = 3 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : (C ^ 3).coeff (3 * C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C * G)).natDegree = 3 * C.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc1 : ((C * G)).coeff (3 * C.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (E ^ 2).natDegree = 3 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (E ^ 2).coeff (3 * C.natDegree) = E.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace6000810_coeff_top
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : E.natDegree + G.natDegree = 2 * C.natDegree + E.natDegree) :
    (xiQuarticChamberFace6000810 A B C D E F G).coeff
        (2 * C.natDegree + E.natDegree) =
      (-15 / 128 : k) * C.leadingCoeff ^ 2 * E.leadingCoeff + (5 / 16 : k) * E.leadingCoeff * G.leadingCoeff := by
  simp only [xiQuarticChamberFace6000810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((C ^ 2 * E)).natDegree = 2 * C.natDegree + E.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((C ^ 2 * E)).coeff (2 * C.natDegree + E.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((E * G)).natDegree = 2 * C.natDegree + E.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc1 : ((E * G)).coeff (2 * C.natDegree + E.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace6005810_coeff_top
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * C.natDegree + G.natDegree = 4 * C.natDegree)
    (ht2 : C.natDegree + 2 * E.natDegree = 4 * C.natDegree)
    (ht3 : 2 * G.natDegree = 4 * C.natDegree) :
    (piQuarticChamberFace6005810 A B C D E F G).coeff
        (4 * C.natDegree) =
      (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (-5 / 8 : k) * C.leadingCoeff * E.leadingCoeff ^ 2 + (5 / 4 : k) * G.leadingCoeff ^ 2 := by
  simp only [piQuarticChamberFace6005810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : (C ^ 4).natDegree = 4 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : (C ^ 4).coeff (4 * C.natDegree) = C.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * G)).natDegree = 4 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * G)).coeff (4 * C.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * E ^ 2)).natDegree = 4 * C.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hEne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((C * E ^ 2)).coeff (4 * C.natDegree) = C.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : (G ^ 2).natDegree = 4 * C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : (G ^ 2).coeff (4 * C.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem n2QuarticChamberFace6000810_coeff_top
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : D.natDegree + G.natDegree = 2 * C.natDegree + D.natDegree) :
    (n2QuarticChamberFace6000810 A B C D E F G).coeff
        (2 * C.natDegree + D.natDegree) =
      (-15 / 128 : k) * C.leadingCoeff ^ 2 * D.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * G.leadingCoeff := by
  simp only [n2QuarticChamberFace6000810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((C ^ 2 * D)).natDegree = 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((C ^ 2 * D)).coeff (2 * C.natDegree + D.natDegree) = C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((D * G)).natDegree = 2 * C.natDegree + D.natDegree := by
    rw [natDegree_mul hDne hGne]
    all_goals omega
  have hc1 : ((D * G)).coeff (2 * C.natDegree + D.natDegree) = D.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace6001810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : E.natDegree + G.natDegree = A.natDegree + D.natDegree + F.natDegree) :
    (xiQuarticChamberFace6001810 A B C D E F G).coeff
        (A.natDegree + D.natDegree + F.natDegree) =
      (-5 / 64 : k) * A.leadingCoeff * D.leadingCoeff * F.leadingCoeff + (5 / 16 : k) * E.leadingCoeff * G.leadingCoeff := by
  simp only [xiQuarticChamberFace6001810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D * F)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    all_goals omega
  have hc0 : ((A * D * F)).coeff (A.natDegree + D.natDegree + F.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((E * G)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc1 : ((E * G)).coeff (A.natDegree + D.natDegree + F.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace6006810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * G.natDegree = A.natDegree + 2 * F.natDegree) :
    (piQuarticChamberFace6006810 A B C D E F G).coeff
        (A.natDegree + 2 * F.natDegree) =
      (-5 / 16 : k) * A.leadingCoeff * F.leadingCoeff ^ 2 + (5 / 4 : k) * G.leadingCoeff ^ 2 := by
  simp only [piQuarticChamberFace6006810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * F ^ 2)).natDegree = A.natDegree + 2 * F.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 2 hFne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * F ^ 2)).coeff (A.natDegree + 2 * F.natDegree) = A.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : (G ^ 2).natDegree = A.natDegree + 2 * F.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : (G ^ 2).coeff (A.natDegree + 2 * F.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem n3QuarticChamberFace6001810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + E.natDegree + F.natDegree = A.natDegree + D.natDegree + G.natDegree) :
    (n3QuarticChamberFace6001810 A B C D E F G).coeff
        (A.natDegree + D.natDegree + G.natDegree) =
      (-15 / 256 : k) * A.leadingCoeff * D.leadingCoeff * G.leadingCoeff + (-15 / 256 : k) * A.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
  simp only [n3QuarticChamberFace6001810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D * G)).natDegree = A.natDegree + D.natDegree + G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hGne, natDegree_mul hAne hDne]
    all_goals omega
  have hc0 : ((A * D * G)).coeff (A.natDegree + D.natDegree + G.natDegree) = A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * E * F)).natDegree = A.natDegree + D.natDegree + G.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hEne) hFne, natDegree_mul hAne hEne]
    all_goals omega
  have hc1 : ((A * E * F)).coeff (A.natDegree + D.natDegree + G.natDegree) = A.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem n4QuarticChamberFace6001810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * A.natDegree + E.natDegree + F.natDegree = 2 * A.natDegree + D.natDegree + G.natDegree) :
    (n4QuarticChamberFace6001810 A B C D E F G).coeff
        (2 * A.natDegree + D.natDegree + G.natDegree) =
      (5 / 256 : k) * A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff + (5 / 256 : k) * A.leadingCoeff ^ 2 * E.leadingCoeff * F.leadingCoeff := by
  simp only [n4QuarticChamberFace6001810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * D * G)).natDegree = 2 * A.natDegree + D.natDegree + G.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * D * G)).coeff (2 * A.natDegree + D.natDegree + G.natDegree) = A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 2 * E * F)).natDegree = 2 * A.natDegree + D.natDegree + G.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hEne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 2 * E * F)).coeff (2 * A.natDegree + D.natDegree + G.natDegree) = A.leadingCoeff ^ 2 * E.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace6004810_coeff_top
    {A B C D E F G : k[X]}
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + G.natDegree = B.natDegree + 2 * C.natDegree)
    (ht2 : D.natDegree + E.natDegree = B.natDegree + 2 * C.natDegree) :
    (kappaQuarticChamberFace6004810 A B C D E F G).coeff
        (B.natDegree + 2 * C.natDegree) =
      (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * E.leadingCoeff := by
  simp only [kappaQuarticChamberFace6004810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((B * C ^ 2)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((B * C ^ 2)).coeff (B.natDegree + 2 * C.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * G)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc1 : ((B * G)).coeff (B.natDegree + 2 * C.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((D * E)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hDne hEne]
    all_goals omega
  have hc2 : ((D * E)).coeff (B.natDegree + 2 * C.natDegree) = D.leadingCoeff * E.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberFace6004810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + B.natDegree + G.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht2 : A.natDegree + D.natDegree + E.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht3 : 2 * C.natDegree + D.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht4 : D.natDegree + G.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree) :
    (nuQuarticChamberFace6004810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + 2 * C.natDegree) =
      (15 / 1024 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 128 : k) * A.leadingCoeff * B.leadingCoeff * G.leadingCoeff + (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff * E.leadingCoeff + (-15 / 128 : k) * C.leadingCoeff ^ 2 * D.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * G.leadingCoeff := by
  simp only [nuQuarticChamberFace6004810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B * C ^ 2)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B * C ^ 2)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * G)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hGne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * G)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * D * E)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    all_goals omega
  have hc2 : ((A * D * E)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((C ^ 2 * D)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((C ^ 2 * D)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((D * G)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hDne hGne]
    all_goals omega
  have hc4 : ((D * G)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = D.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4]
  ring

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace6002810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * C.natDegree + E.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree)
    (ht2 : C.natDegree + 2 * D.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree)
    (ht3 : E.natDegree + G.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree) :
    (xiQuarticChamberFace6002810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + C.natDegree + D.natDegree) =
      (15 / 256 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff + (-15 / 128 : k) * C.leadingCoeff ^ 2 * E.leadingCoeff + (-15 / 128 : k) * C.leadingCoeff * D.leadingCoeff ^ 2 + (5 / 16 : k) * E.leadingCoeff * G.leadingCoeff := by
  simp only [xiQuarticChamberFace6002810, coeff_add, coeff_sub,
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
  have hd2 : ((C * D ^ 2)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((C * D ^ 2)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((E * G)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc3 : ((E * G)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberFace6004810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * A.natDegree + B.natDegree + G.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht2 : 2 * A.natDegree + D.natDegree + E.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht3 : A.natDegree + 2 * C.natDegree + D.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht4 : A.natDegree + D.natDegree + G.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree) :
    (omicronQuarticChamberFace6004810 A B C D E F G).coeff
        (2 * A.natDegree + B.natDegree + 2 * C.natDegree) =
      (15 / 16384 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff + (15 / 1024 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff + (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
  simp only [omicronQuarticChamberFace6004810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B * C ^ 2)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B * C ^ 2)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 2 * B * G)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 2 * B * G)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A ^ 2 * D * E)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A ^ 2 * D * E)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A * C ^ 2 * D)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((A * C ^ 2 * D)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((A * D * G)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hGne, natDegree_mul hAne hDne]
    all_goals omega
  have hc4 : ((A * D * G)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4]
  ring

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberFace6004810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * A.natDegree + B.natDegree + G.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht2 : 3 * A.natDegree + D.natDegree + E.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht3 : 2 * A.natDegree + 2 * C.natDegree + D.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht4 : 2 * A.natDegree + D.natDegree + G.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree) :
    (primitiveQuarticChamberFace6004810 A B C D E F G).coeff
        (3 * A.natDegree + B.natDegree + 2 * C.natDegree) =
      (15 / 16384 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff + (15 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff + (-5 / 256 : k) * A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
  simp only [primitiveQuarticChamberFace6004810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 3 * B * C ^ 2)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 3 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 3 * B * C ^ 2)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 3 * B * G)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 3 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 3 * B * G)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A ^ 3 * D * E)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 3 hAne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A ^ 3 * D * E)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A ^ 2 * C ^ 2 * D)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((A ^ 2 * C ^ 2 * D)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((A ^ 2 * D * G)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : ((A ^ 2 * D * G)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4]
  ring

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace6005810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + 2 * C.natDegree = A.natDegree + 3 * B.natDegree)
    (ht2 : B.natDegree + G.natDegree = A.natDegree + 3 * B.natDegree)
    (ht3 : C.natDegree + F.natDegree = A.natDegree + 3 * B.natDegree) :
    (kappaQuarticChamberFace6005810 A B C D E F G).coeff
        (A.natDegree + 3 * B.natDegree) =
      (5 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 3 + (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff + (5 / 16 : k) * C.leadingCoeff * F.leadingCoeff := by
  simp only [kappaQuarticChamberFace6005810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 3)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 3)).coeff (A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * C ^ 2)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B * C ^ 2)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((B * G)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc2 : ((B * G)).coeff (A.natDegree + 3 * B.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((C * F)).natDegree = A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc3 : ((C * F)).coeff (A.natDegree + 3 * B.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem muQuarticChamberFace6005810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + B.natDegree + F.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht2 : 3 * C.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree)
    (ht3 : C.natDegree + G.natDegree = A.natDegree + 2 * B.natDegree + C.natDegree) :
    (muQuarticChamberFace6005810 A B C D E F G).coeff
        (A.natDegree + 2 * B.natDegree + C.natDegree) =
      (15 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff + (-5 / 64 : k) * A.leadingCoeff * B.leadingCoeff * F.leadingCoeff + (-5 / 128 : k) * C.leadingCoeff ^ 3 + (5 / 16 : k) * C.leadingCoeff * G.leadingCoeff := by
  simp only [muQuarticChamberFace6005810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 2 * C)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 2 * C)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * F)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hFne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * F)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = A.leadingCoeff * B.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : (C ^ 3).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : (C ^ 3).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff ^ 3 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((C * G)).natDegree = A.natDegree + 2 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hCne hGne]
    all_goals omega
  have hc3 : ((C * G)).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = C.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberFace6005810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + B.natDegree + 2 * C.natDegree = 2 * A.natDegree + 3 * B.natDegree)
    (ht2 : A.natDegree + B.natDegree + G.natDegree = 2 * A.natDegree + 3 * B.natDegree)
    (ht3 : A.natDegree + C.natDegree + F.natDegree = 2 * A.natDegree + 3 * B.natDegree) :
    (nuQuarticChamberFace6005810 A B C D E F G).coeff
        (2 * A.natDegree + 3 * B.natDegree) =
      (-5 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 + (15 / 1024 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 128 : k) * A.leadingCoeff * B.leadingCoeff * G.leadingCoeff + (-5 / 128 : k) * A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
  simp only [nuQuarticChamberFace6005810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * B * G)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hGne, natDegree_mul hAne hBne]
    all_goals omega
  have hc2 : ((A * B * G)).coeff (2 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A * C * F)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) hFne, natDegree_mul hAne hCne]
    all_goals omega
  have hc3 : ((A * C * F)).coeff (2 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace6003810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * B.natDegree + 2 * C.natDegree = A.natDegree + 4 * B.natDegree)
    (ht2 : 2 * B.natDegree + G.natDegree = A.natDegree + 4 * B.natDegree)
    (ht3 : B.natDegree + C.natDegree + F.natDegree = A.natDegree + 4 * B.natDegree)
    (ht4 : 2 * F.natDegree = A.natDegree + 4 * B.natDegree) :
    (xiQuarticChamberFace6003810 A B C D E F G).coeff
        (A.natDegree + 4 * B.natDegree) =
      (-15 / 2048 : k) * A.leadingCoeff * B.leadingCoeff ^ 4 + (45 / 512 : k) * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 + (-5 / 64 : k) * B.leadingCoeff ^ 2 * G.leadingCoeff + (-25 / 128 : k) * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (5 / 32 : k) * F.leadingCoeff ^ 2 := by
  simp only [xiQuarticChamberFace6003810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B ^ 4)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 4 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B ^ 4)).coeff (A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 4 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B ^ 2 * C ^ 2)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((B ^ 2 * C ^ 2)).coeff (A.natDegree + 4 * B.natDegree) = B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((B ^ 2 * G)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hBne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((B ^ 2 * G)).coeff (A.natDegree + 4 * B.natDegree) = B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((B * C * F)).natDegree = A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) hFne, natDegree_mul hBne hCne]
    all_goals omega
  have hc3 : ((B * C * F)).coeff (A.natDegree + 4 * B.natDegree) = B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : (F ^ 2).natDegree = A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : (F ^ 2).coeff (A.natDegree + 4 * B.natDegree) = F.leadingCoeff ^ 2 := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4]
  ring

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberFace6005810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * A.natDegree + B.natDegree + 2 * C.natDegree = 3 * A.natDegree + 3 * B.natDegree)
    (ht2 : 2 * A.natDegree + B.natDegree + G.natDegree = 3 * A.natDegree + 3 * B.natDegree)
    (ht3 : 2 * A.natDegree + C.natDegree + F.natDegree = 3 * A.natDegree + 3 * B.natDegree) :
    (omicronQuarticChamberFace6005810 A B C D E F G).coeff
        (3 * A.natDegree + 3 * B.natDegree) =
      (-5 / 65536 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 + (15 / 16384 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
  simp only [omicronQuarticChamberFace6005810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 3 * B ^ 3)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 3 * B ^ 3)).coeff (3 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 2 * B * C ^ 2)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 2 * B * C ^ 2)).coeff (3 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A ^ 2 * B * G)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A ^ 2 * B * G)).coeff (3 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A ^ 2 * C * F)).natDegree = 3 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((A ^ 2 * C * F)).coeff (3 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem piQuarticChamberFace6007810_coeff_top
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
    (piQuarticChamberFace6007810 A B C D E F G).coeff
        (2 * A.natDegree + 4 * B.natDegree) =
      (15 / 4096 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff ^ 4 + (-45 / 512 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 + (5 / 64 : k) * A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 32 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (-5 / 16 : k) * A.leadingCoeff * F.leadingCoeff ^ 2 + (15 / 256 : k) * C.leadingCoeff ^ 4 + (-5 / 16 : k) * C.leadingCoeff ^ 2 * G.leadingCoeff + (5 / 4 : k) * G.leadingCoeff ^ 2 := by
  simp only [piQuarticChamberFace6007810, coeff_add, coeff_sub,
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
  have hd2 : ((A * B ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hGne, natDegree_mul hAne (pow_ne_zero 2 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A * B ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A * B * C * F)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc3 : ((A * B * C * F)).coeff (2 * A.natDegree + 4 * B.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
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
  have hd6 : ((C ^ 2 * G)).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hGne]
    simp only [natDegree_pow]
    all_goals omega
  have hc6 : ((C ^ 2 * G)).coeff (2 * A.natDegree + 4 * B.natDegree) = C.leadingCoeff ^ 2 * G.leadingCoeff := by
    rw [← hd6, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd7 : (G ^ 2).natDegree = 2 * A.natDegree + 4 * B.natDegree := by
    simp only [natDegree_pow]
    all_goals omega
  have hc7 : (G ^ 2).coeff (2 * A.natDegree + 4 * B.natDegree) = G.leadingCoeff ^ 2 := by
    rw [← hd7, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
  ring

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberFace6005810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * A.natDegree + B.natDegree + 2 * C.natDegree = 4 * A.natDegree + 3 * B.natDegree)
    (ht2 : 3 * A.natDegree + B.natDegree + G.natDegree = 4 * A.natDegree + 3 * B.natDegree)
    (ht3 : 3 * A.natDegree + C.natDegree + F.natDegree = 4 * A.natDegree + 3 * B.natDegree) :
    (primitiveQuarticChamberFace6005810 A B C D E F G).coeff
        (4 * A.natDegree + 3 * B.natDegree) =
      (-5 / 65536 : k) * A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 + (15 / 16384 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff := by
  simp only [primitiveQuarticChamberFace6005810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 4 * B ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) (pow_ne_zero 3 hBne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 4 * B ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 3 * B * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 3 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 3 * B * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A ^ 3 * B * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 3 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A ^ 3 * B * G)).coeff (4 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A ^ 3 * C * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 3 hAne) hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((A ^ 3 * C * F)).coeff (4 * A.natDegree + 3 * B.natDegree) = A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace6006810_coeff_top
    {A B C D E F G : k[X]}
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + G.natDegree = B.natDegree + 2 * C.natDegree)
    (ht2 : C.natDegree + F.natDegree = B.natDegree + 2 * C.natDegree) :
    (kappaQuarticChamberFace6006810 A B C D E F G).coeff
        (B.natDegree + 2 * C.natDegree) =
      (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff + (5 / 16 : k) * C.leadingCoeff * F.leadingCoeff := by
  simp only [kappaQuarticChamberFace6006810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((B * C ^ 2)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((B * C ^ 2)).coeff (B.natDegree + 2 * C.natDegree) = B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((B * G)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hBne hGne]
    all_goals omega
  have hc1 : ((B * G)).coeff (B.natDegree + 2 * C.natDegree) = B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * F)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc2 : ((C * F)).coeff (B.natDegree + 2 * C.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberFace6006810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + B.natDegree + G.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht2 : A.natDegree + C.natDegree + F.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht3 : 2 * C.natDegree + D.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht4 : D.natDegree + G.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree) :
    (nuQuarticChamberFace6006810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + 2 * C.natDegree) =
      (15 / 1024 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 128 : k) * A.leadingCoeff * B.leadingCoeff * G.leadingCoeff + (-5 / 128 : k) * A.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (-15 / 128 : k) * C.leadingCoeff ^ 2 * D.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * G.leadingCoeff := by
  simp only [nuQuarticChamberFace6006810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B * C ^ 2)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A * B * C ^ 2)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * B * G)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) hGne, natDegree_mul hAne hBne]
    all_goals omega
  have hc1 : ((A * B * G)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * C * F)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) hFne, natDegree_mul hAne hCne]
    all_goals omega
  have hc2 : ((A * C * F)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((C ^ 2 * D)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((C ^ 2 * D)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((D * G)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hDne hGne]
    all_goals omega
  have hc4 : ((D * G)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = D.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4]
  ring

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace6004810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : A.natDegree + D.natDegree + F.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree)
    (ht2 : C.natDegree + 2 * D.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree) :
    (xiQuarticChamberFace6004810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + C.natDegree + D.natDegree) =
      (15 / 256 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff + (-5 / 64 : k) * A.leadingCoeff * D.leadingCoeff * F.leadingCoeff + (-15 / 128 : k) * C.leadingCoeff * D.leadingCoeff ^ 2 := by
  simp only [xiQuarticChamberFace6004810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * B * C * D)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hDne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    all_goals omega
  have hc0 : ((A * B * C * D)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * D * F)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    all_goals omega
  have hc1 : ((A * D * F)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * D ^ 2)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((C * D ^ 2)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2]
  ring

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberFace6006810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * A.natDegree + B.natDegree + G.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht2 : 2 * A.natDegree + C.natDegree + F.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht3 : A.natDegree + 2 * C.natDegree + D.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht4 : A.natDegree + D.natDegree + G.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree) :
    (omicronQuarticChamberFace6006810 A B C D E F G).coeff
        (2 * A.natDegree + B.natDegree + 2 * C.natDegree) =
      (15 / 16384 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff + (15 / 1024 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff + (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
  simp only [omicronQuarticChamberFace6006810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * B * C ^ 2)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * B * C ^ 2)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 2 * B * G)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 2 * B * G)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A ^ 2 * C * F)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A ^ 2 * C * F)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A * C ^ 2 * D)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((A * C ^ 2 * D)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((A * D * G)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hGne, natDegree_mul hAne hDne]
    all_goals omega
  have hc4 : ((A * D * G)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4]
  ring

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberFace6006810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * A.natDegree + B.natDegree + G.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht2 : 3 * A.natDegree + C.natDegree + F.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht3 : 2 * A.natDegree + 2 * C.natDegree + D.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht4 : 2 * A.natDegree + D.natDegree + G.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree) :
    (primitiveQuarticChamberFace6006810 A B C D E F G).coeff
        (3 * A.natDegree + B.natDegree + 2 * C.natDegree) =
      (15 / 16384 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff + (15 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff + (-5 / 256 : k) * A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
  simp only [primitiveQuarticChamberFace6006810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 3 * B * C ^ 2)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 3 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 3 * B * C ^ 2)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 3 * B * G)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 3 hAne) hBne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 3 * B * G)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A ^ 3 * C * F)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 3 hAne) hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A ^ 3 * C * F)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A ^ 2 * C ^ 2 * D)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((A ^ 2 * C ^ 2 * D)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((A ^ 2 * D * G)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : ((A ^ 2 * D * G)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4]
  ring

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace6007810_coeff_top
    {A B C D E F G : k[X]}
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (ht1 : D.natDegree + E.natDegree = C.natDegree + F.natDegree) :
    (kappaQuarticChamberFace6007810 A B C D E F G).coeff
        (C.natDegree + F.natDegree) =
      (5 / 16 : k) * C.leadingCoeff * F.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * E.leadingCoeff := by
  simp only [kappaQuarticChamberFace6007810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((C * F)).natDegree = C.natDegree + F.natDegree := by
    rw [natDegree_mul hCne hFne]
    all_goals omega
  have hc0 : ((C * F)).coeff (C.natDegree + F.natDegree) = C.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((D * E)).natDegree = C.natDegree + F.natDegree := by
    rw [natDegree_mul hDne hEne]
    all_goals omega
  have hc1 : ((D * E)).coeff (C.natDegree + F.natDegree) = D.leadingCoeff * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1]
  ring


end QuarticChamberUnownedSystemBridges1810

end Max11DegreeRoutes
