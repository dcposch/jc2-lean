import Grok810ScaleZeroQuarticChamberUnownedSystemPackets2Scratch

/-! # `_coeff_top` bridges for the unowned systems, part 2/2

9 of the 62 top-coefficient bridges, one per (carrier,
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

section QuarticChamberUnownedSystemBridges2810

/-! ## Top-coefficient bridges -/

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberFace6007810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + D.natDegree + E.natDegree = A.natDegree + C.natDegree + F.natDegree)
    (ht2 : 2 * C.natDegree + D.natDegree = A.natDegree + C.natDegree + F.natDegree)
    (ht3 : D.natDegree + G.natDegree = A.natDegree + C.natDegree + F.natDegree) :
    (nuQuarticChamberFace6007810 A B C D E F G).coeff
        (A.natDegree + C.natDegree + F.natDegree) =
      (-5 / 128 : k) * A.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff * E.leadingCoeff + (-15 / 128 : k) * C.leadingCoeff ^ 2 * D.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * G.leadingCoeff := by
  simp only [nuQuarticChamberFace6007810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * C * F)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hCne) hFne, natDegree_mul hAne hCne]
    all_goals omega
  have hc0 : ((A * C * F)).coeff (A.natDegree + C.natDegree + F.natDegree) = A.leadingCoeff * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A * D * E)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    all_goals omega
  have hc1 : ((A * D * E)).coeff (A.natDegree + C.natDegree + F.natDegree) = A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C ^ 2 * D)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((C ^ 2 * D)).coeff (A.natDegree + C.natDegree + F.natDegree) = C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((D * G)).natDegree = A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul hDne hGne]
    all_goals omega
  have hc3 : ((D * G)).coeff (A.natDegree + C.natDegree + F.natDegree) = D.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace6005810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * C.natDegree + E.natDegree = A.natDegree + D.natDegree + F.natDegree)
    (ht2 : C.natDegree + 2 * D.natDegree = A.natDegree + D.natDegree + F.natDegree)
    (ht3 : E.natDegree + G.natDegree = A.natDegree + D.natDegree + F.natDegree) :
    (xiQuarticChamberFace6005810 A B C D E F G).coeff
        (A.natDegree + D.natDegree + F.natDegree) =
      (-5 / 64 : k) * A.leadingCoeff * D.leadingCoeff * F.leadingCoeff + (-15 / 128 : k) * C.leadingCoeff ^ 2 * E.leadingCoeff + (-15 / 128 : k) * C.leadingCoeff * D.leadingCoeff ^ 2 + (5 / 16 : k) * E.leadingCoeff * G.leadingCoeff := by
  simp only [xiQuarticChamberFace6005810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A * D * F)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hFne, natDegree_mul hAne hDne]
    all_goals omega
  have hc0 : ((A * D * F)).coeff (A.natDegree + D.natDegree + F.natDegree) = A.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((C ^ 2 * E)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((C ^ 2 * E)).coeff (A.natDegree + D.natDegree + F.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((C * D ^ 2)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((C * D ^ 2)).coeff (A.natDegree + D.natDegree + F.natDegree) = C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((E * G)).natDegree = A.natDegree + D.natDegree + F.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc3 : ((E * G)).coeff (A.natDegree + D.natDegree + F.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberFace6007810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * A.natDegree + D.natDegree + E.natDegree = 2 * A.natDegree + C.natDegree + F.natDegree)
    (ht2 : A.natDegree + 2 * C.natDegree + D.natDegree = 2 * A.natDegree + C.natDegree + F.natDegree)
    (ht3 : A.natDegree + D.natDegree + G.natDegree = 2 * A.natDegree + C.natDegree + F.natDegree) :
    (omicronQuarticChamberFace6007810 A B C D E F G).coeff
        (2 * A.natDegree + C.natDegree + F.natDegree) =
      (-5 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff + (15 / 1024 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff + (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
  simp only [omicronQuarticChamberFace6007810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 2 * C * F)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 2 * C * F)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) = A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 2 * D * E)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 2 * D * E)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) = A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A * C ^ 2 * D)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A * C ^ 2 * D)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) = A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A * D * G)).natDegree = 2 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hGne, natDegree_mul hAne hDne]
    all_goals omega
  have hc3 : ((A * D * G)).coeff (2 * A.natDegree + C.natDegree + F.natDegree) = A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberFace6007810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * A.natDegree + D.natDegree + E.natDegree = 3 * A.natDegree + C.natDegree + F.natDegree)
    (ht2 : 2 * A.natDegree + 2 * C.natDegree + D.natDegree = 3 * A.natDegree + C.natDegree + F.natDegree)
    (ht3 : 2 * A.natDegree + D.natDegree + G.natDegree = 3 * A.natDegree + C.natDegree + F.natDegree) :
    (primitiveQuarticChamberFace6007810 A B C D E F G).coeff
        (3 * A.natDegree + C.natDegree + F.natDegree) =
      (-5 / 2048 : k) * A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff + (15 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff + (-5 / 256 : k) * A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
  simp only [primitiveQuarticChamberFace6007810, coeff_add, coeff_sub,
    coeff_smul, smul_eq_mul]
  have hd0 : ((A ^ 3 * C * F)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 3 hAne) hCne]
    simp only [natDegree_pow]
    all_goals omega
  have hc0 : ((A ^ 3 * C * F)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) = A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hd0, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd1 : ((A ^ 3 * D * E)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 3 hAne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc1 : ((A ^ 3 * D * E)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) = A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd1, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd2 : ((A ^ 2 * C ^ 2 * D)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((A ^ 2 * C ^ 2 * D)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) = A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((A ^ 2 * D * G)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((A ^ 2 * D * G)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) = A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem kappaQuarticChamberFace6008810_coeff_top
    {A B C D E F G : k[X]}
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : B.natDegree + G.natDegree = B.natDegree + 2 * C.natDegree)
    (ht2 : C.natDegree + F.natDegree = B.natDegree + 2 * C.natDegree)
    (ht3 : D.natDegree + E.natDegree = B.natDegree + 2 * C.natDegree) :
    (kappaQuarticChamberFace6008810 A B C D E F G).coeff
        (B.natDegree + 2 * C.natDegree) =
      (-15 / 128 : k) * B.leadingCoeff * C.leadingCoeff ^ 2 + (5 / 16 : k) * B.leadingCoeff * G.leadingCoeff + (5 / 16 : k) * C.leadingCoeff * F.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * E.leadingCoeff := by
  simp only [kappaQuarticChamberFace6008810, coeff_add, coeff_sub,
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
  have hd3 : ((D * E)).natDegree = B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hDne hEne]
    all_goals omega
  have hc3 : ((D * E)).coeff (B.natDegree + 2 * C.natDegree) = D.leadingCoeff * E.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3]
  ring

set_option maxHeartbeats 64000000 in
theorem nuQuarticChamberFace6008810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + B.natDegree + G.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht2 : A.natDegree + C.natDegree + F.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht3 : A.natDegree + D.natDegree + E.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht4 : 2 * C.natDegree + D.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht5 : D.natDegree + G.natDegree = A.natDegree + B.natDegree + 2 * C.natDegree) :
    (nuQuarticChamberFace6008810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + 2 * C.natDegree) =
      (15 / 1024 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 128 : k) * A.leadingCoeff * B.leadingCoeff * G.leadingCoeff + (-5 / 128 : k) * A.leadingCoeff * C.leadingCoeff * F.leadingCoeff + (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff * E.leadingCoeff + (-15 / 128 : k) * C.leadingCoeff ^ 2 * D.leadingCoeff + (5 / 16 : k) * D.leadingCoeff * G.leadingCoeff := by
  simp only [nuQuarticChamberFace6008810, coeff_add, coeff_sub,
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
  have hd3 : ((A * D * E)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hEne, natDegree_mul hAne hDne]
    all_goals omega
  have hc3 : ((A * D * E)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((C ^ 2 * D)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : ((C ^ 2 * D)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : ((D * G)).natDegree = A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul hDne hGne]
    all_goals omega
  have hc5 : ((D * G)).coeff (A.natDegree + B.natDegree + 2 * C.natDegree) = D.leadingCoeff * G.leadingCoeff := by
    rw [← hd5, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4, hc5]
  ring

set_option maxHeartbeats 64000000 in
theorem xiQuarticChamberFace6006810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : A.natDegree + D.natDegree + F.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree)
    (ht2 : 2 * C.natDegree + E.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree)
    (ht3 : C.natDegree + 2 * D.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree)
    (ht4 : E.natDegree + G.natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree) :
    (xiQuarticChamberFace6006810 A B C D E F G).coeff
        (A.natDegree + B.natDegree + C.natDegree + D.natDegree) =
      (15 / 256 : k) * A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * D.leadingCoeff + (-5 / 64 : k) * A.leadingCoeff * D.leadingCoeff * F.leadingCoeff + (-15 / 128 : k) * C.leadingCoeff ^ 2 * E.leadingCoeff + (-15 / 128 : k) * C.leadingCoeff * D.leadingCoeff ^ 2 + (5 / 16 : k) * E.leadingCoeff * G.leadingCoeff := by
  simp only [xiQuarticChamberFace6006810, coeff_add, coeff_sub,
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
  have hd2 : ((C ^ 2 * E)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hEne]
    simp only [natDegree_pow]
    all_goals omega
  have hc2 : ((C ^ 2 * E)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hd2, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd3 : ((C * D ^ 2)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul hCne (pow_ne_zero 2 hDne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((C * D ^ 2)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((E * G)).natDegree = A.natDegree + B.natDegree + C.natDegree + D.natDegree := by
    rw [natDegree_mul hEne hGne]
    all_goals omega
  have hc4 : ((E * G)).coeff (A.natDegree + B.natDegree + C.natDegree + D.natDegree) = E.leadingCoeff * G.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4]
  ring

set_option maxHeartbeats 64000000 in
theorem omicronQuarticChamberFace6008810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 2 * A.natDegree + B.natDegree + G.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht2 : 2 * A.natDegree + C.natDegree + F.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht3 : 2 * A.natDegree + D.natDegree + E.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht4 : A.natDegree + 2 * C.natDegree + D.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht5 : A.natDegree + D.natDegree + G.natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree) :
    (omicronQuarticChamberFace6008810 A B C D E F G).coeff
        (2 * A.natDegree + B.natDegree + 2 * C.natDegree) =
      (15 / 16384 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * B.leadingCoeff * G.leadingCoeff + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff * F.leadingCoeff + (-5 / 2048 : k) * A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff + (15 / 1024 : k) * A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff + (-5 / 128 : k) * A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
  simp only [omicronQuarticChamberFace6008810, coeff_add, coeff_sub,
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
  have hd3 : ((A ^ 2 * D * E)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hAne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((A ^ 2 * D * E)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((A * C ^ 2 * D)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hCne)) hDne, natDegree_mul hAne (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : ((A * C ^ 2 * D)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : ((A * D * G)).natDegree = 2 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hDne) hGne, natDegree_mul hAne hDne]
    all_goals omega
  have hc5 : ((A * D * G)).coeff (2 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hd5, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4, hc5]
  ring

set_option maxHeartbeats 64000000 in
theorem primitiveQuarticChamberFace6008810_coeff_top
    {A B C D E F G : k[X]}
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    (ht1 : 3 * A.natDegree + B.natDegree + G.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht2 : 3 * A.natDegree + C.natDegree + F.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht3 : 3 * A.natDegree + D.natDegree + E.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht4 : 2 * A.natDegree + 2 * C.natDegree + D.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree)
    (ht5 : 2 * A.natDegree + D.natDegree + G.natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree) :
    (primitiveQuarticChamberFace6008810 A B C D E F G).coeff
        (3 * A.natDegree + B.natDegree + 2 * C.natDegree) =
      (15 / 16384 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff + (-5 / 2048 : k) * A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff + (15 / 2048 : k) * A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff + (-5 / 256 : k) * A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
  simp only [primitiveQuarticChamberFace6008810, coeff_add, coeff_sub,
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
  have hd3 : ((A ^ 3 * D * E)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 3 hAne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc3 : ((A ^ 3 * D * E)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hd3, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd4 : ((A ^ 2 * C ^ 2 * D)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)]
    simp only [natDegree_pow]
    all_goals omega
  have hc4 : ((A ^ 2 * C ^ 2 * D)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hd4, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  have hd5 : ((A ^ 2 * D * G)).natDegree = 3 * A.natDegree + B.natDegree + 2 * C.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne]
    simp only [natDegree_pow]
    all_goals omega
  have hc5 : ((A ^ 2 * D * G)).coeff (3 * A.natDegree + B.natDegree + 2 * C.natDegree) = A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hd5, coeff_natDegree]
    simp only [leadingCoeff_mul, leadingCoeff_pow]
  rw [hc0, hc1, hc2, hc3, hc4, hc5]
  ring


end QuarticChamberUnownedSystemBridges2810

end Max11DegreeRoutes
