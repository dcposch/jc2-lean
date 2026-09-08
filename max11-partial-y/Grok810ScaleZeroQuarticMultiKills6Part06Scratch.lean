import Grok810ScaleZeroQuarticMultiKills6Part05Scratch

/-! # Part 6 of `Grok810ScaleZeroQuarticMultiKills6Scratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills6Scratch`; statements are byte-identical.
-/

open scoped Polynomial.Bivariate

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxRecDepth 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.flexible false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 32000000 in
theorem degreeZeroPrimitiveQuarticNoABCDEG810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G) :
    (degreeZeroPrimitiveQuarticNoABCDEG810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  rw [speedRefl_degreeZeroPrimitiveQuarticNoABCDEG810_eq_polyOf]
  refine Max11ReflectDeg.natDegree_polyOf_lt_of_degOk (by omega) ?_
  simp only [Max11ReflectDeg.degOk_cons, Max11ReflectDeg.degOk_nil_left,
    Max11ReflectDeg.degOk_nil_right, Max11ReflectDeg.mdeg_cons,
    Max11ReflectDeg.mdeg_nil_left, Max11ReflectDeg.mdeg_nil_right,
    List.map_cons, List.map_nil, mul_zero, zero_mul, neg_zero,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
    mul_one, one_mul, and_true, true_and, natDegree_zero]
  repeat' apply And.intro
  all_goals first
    | (right; right; omega)
    | (left; norm_num; done)
    | (right; left; simp; done)
    | trivial

theorem primitiveQuarticFaceABCDEG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hGne : G ≠ 0)
    : (primitiveQuarticFaceABCDEG810 A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * primitiveQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
  simp only [primitiveQuarticFaceABCDEG810, primitiveQuarticInnerABCDEG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A4B3 : ((A ^ 4 * B ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A4B3 : ((A ^ 4 * B ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 4 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A4B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3B2D : ((A ^ 3 * B ^ 2 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne)) hDne, natDegree_mul (pow_ne_zero 3 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A3B2D : ((A ^ 3 * B ^ 2 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A3B2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3BC2 : ((A ^ 3 * B * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) (pow_ne_zero 2 hCne), natDegree_mul (pow_ne_zero 3 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A3BC2 : ((A ^ 3 * B * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_A3BC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A3BG : ((A ^ 3 * B * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hBne) hGne, natDegree_mul (pow_ne_zero 3 hAne) hBne, natDegree_pow]
    omega
  have hcf_A3BG : ((A ^ 3 * B * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * B.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A3BG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A3DE : ((A ^ 3 * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 3 hAne) hDne, natDegree_pow]
    omega
  have hcf_A3DE : ((A ^ 3 * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A3DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2B3C : ((A ^ 2 * B ^ 3 * C)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne)) hCne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B3C : ((A ^ 2 * B ^ 3 * C)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_A2B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BCE : ((A ^ 2 * B * C * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hCne) hEne, natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) hCne, natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow]
    omega
  have hcf_A2BCE : ((A ^ 2 * B * C * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * C.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A2BCE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2BD2 : ((A ^ 2 * B * D ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hDne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A2BD2 : ((A ^ 2 * B * D ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2C2D : ((A ^ 2 * C ^ 2 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2C2D : ((A ^ 2 * C ^ 2 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2DG : ((A ^ 2 * D * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DG : ((A ^ 2 * D * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A2DG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB5 : ((A * B ^ 5)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 5 hBne), natDegree_pow]
    omega
  have hcf_AB5 : ((A * B ^ 5)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 5 := by
    rw [← hdeg_AB5, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB3E : ((A * B ^ 3 * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne (pow_ne_zero 3 hBne)) hEne, natDegree_mul hAne (pow_ne_zero 3 hBne), natDegree_pow]
    omega
  have hcf_AB3E : ((A * B ^ 3 * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 3 * E.leadingCoeff := by
    rw [← hdeg_AB3E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AB2CD : ((A * B ^ 2 * C * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne) hDne, natDegree_mul (mul_ne_zero hAne (pow_ne_zero 2 hBne)) hCne, natDegree_mul hAne (pow_ne_zero 2 hBne), natDegree_pow]
    omega
  have hcf_AB2CD : ((A * B ^ 2 * C * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff ^ 2 * C.leadingCoeff * D.leadingCoeff := by
    rw [← hdeg_AB2CD, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABC3 : ((A * B * C ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 3 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC3 : ((A * B * C ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_ABC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ABCG : ((A * B * C * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hCne) hGne, natDegree_mul (mul_ne_zero hAne hBne) hCne, natDegree_mul hAne hBne]
    omega
  have hcf_ABCG : ((A * B * C * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_ABCG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABE2 : ((A * B * E ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hEne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABE2 : ((A * B * E ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_ABE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ACDE : ((A * C * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hCne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hCne) hDne, natDegree_mul hAne hCne]
    omega
  have hcf_ACDE : ((A * C * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ACDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AD3 : ((A * D ^ 3)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hDne), natDegree_pow]
    omega
  have hcf_AD3 : ((A * D ^ 3)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 3 := by
    rw [← hdeg_AD3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B4D : ((B ^ 4 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 4 hBne) hDne, natDegree_pow]
    omega
  have hcf_B4D : ((B ^ 4 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 4 * D.leadingCoeff := by
    rw [← hdeg_B4D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3C2 : ((B ^ 3 * C ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_B3C2 : ((B ^ 3 * C ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff ^ 2 := by
    rw [← hdeg_B3C2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_B3G : ((B ^ 3 * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hGne, natDegree_pow]
    omega
  have hcf_B3G : ((B ^ 3 * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * G.leadingCoeff := by
    rw [← hdeg_B3G, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B2DE : ((B ^ 2 * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2DE : ((B ^ 2 * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BC2E : ((B * C ^ 2 * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne (pow_ne_zero 2 hCne)) hEne, natDegree_mul hBne (pow_ne_zero 2 hCne), natDegree_pow]
    omega
  have hcf_BC2E : ((B * C ^ 2 * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 2 * E.leadingCoeff := by
    rw [← hdeg_BC2E, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BCD2 : ((B * C * D ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hCne) (pow_ne_zero 2 hDne), natDegree_mul hBne hCne, natDegree_pow]
    omega
  have hcf_BCD2 : ((B * C * D ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BCD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BEG : ((B * E * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hBne hEne) hGne, natDegree_mul hBne hEne]
    omega
  have hcf_BEG : ((B * E * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * E.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_BEG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3D : ((C ^ 3 * D)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hCne) hDne, natDegree_pow]
    omega
  have hcf_C3D : ((C ^ 3 * D)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_C3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDG : ((C * D * G)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hGne, natDegree_mul hCne hDne]
    omega
  have hcf_CDG : ((C * D * G)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      C.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_DE2 : ((D * E ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_DE2 : ((D * E ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_DE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A4B3, hcf_A3B2D, hcf_A3BC2, hcf_A3BG, hcf_A3DE, hcf_A2B3C, hcf_A2BCE, hcf_A2BD2, hcf_A2C2D, hcf_A2DG, hcf_AB5, hcf_AB3E, hcf_AB2CD, hcf_ABC3, hcf_ABCG, hcf_ABE2, hcf_ACDE, hcf_AD3, hcf_B4D, hcf_B3C2, hcf_B3G, hcf_B2DE, hcf_BC2E, hcf_BCD2, hcf_BEG, hcf_C3D, hcf_CDG, hcf_DE2]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_ABCDEG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABCDEG810 A B C D E F G)
    (hxi : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hmu : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (homi : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hkap : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        0)
    (hnu : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hpi : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta
          theta A B C D E F G).natDegree =
        0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveQuarticInnerABCDEG810 A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveQuarticNoABCDEG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := primitiveQuarticFaceABCDEG810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hGne := hGne)
    have hz : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hCpos, hDpos, hEpos, hGpos, hAB, hAC, hAD, hAE, hAG, hFlt⟩
      omega
    rw [degreeZeroPrimitiveQuartic810_eq_ABCDEG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_ABCDEG_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff G.leadingCoeff
  have hpow : D.leadingCoeff ^ 6 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hDne
  exact hlc ((pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hpow)

def kappaQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d + (-60 : k) * b * c ^ 2 + 160 * b * g + 160 * c * f

def muQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  60 * a * b ^ 2 * c + (-160 : k) * a * b * f + (-80 : k) * a * d ^ 2 + 35 * b ^ 4 + (-480 : k) * b * c * d + (-80 : k) * c ^ 3 + 640 * c * g + 640 * d * f

def nuQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + 60 * a * b * c ^ 2 + (-160 : k) * a * b * g + (-160 : k) * a * c * f + 280 * b ^ 3 * c + (-480 : k) * b ^ 2 * f + (-480 : k) * b * d ^ 2 + (-480 : k) * c ^ 2 * d + 1280 * d * g

def xiQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  (-15 : k) * a * b ^ 4 + 120 * a * b * c * d + (-160 : k) * a * d * f + 110 * b ^ 3 * d + 180 * b ^ 2 * c ^ 2 + (-160 : k) * b ^ 2 * g + (-400 : k) * b * c * f + (-240 : k) * c * d ^ 2 + 320 * f ^ 2

def omicronQuarticInnerABCDFG810 (a b c d f g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + 60 * a ^ 2 * b * c ^ 2 + (-160 : k) * a ^ 2 * b * g + (-160 : k) * a ^ 2 * c * f + (-1120 : k) * a * b ^ 3 * c + 1600 * a * b ^ 2 * f + 2240 * a * b * d ^ 2 + 960 * a * c ^ 2 * d + (-2560 : k) * a * d * g + (-336 : k) * b ^ 5 + 8640 * b ^ 2 * c * d + 2880 * b * c ^ 3 + (-7680 : k) * b * c * g + (-10240 : k) * b * d * f + (-5120 : k) * c ^ 2 * f + (-2560 : k) * d ^ 3 + 20480 * f * g

end QuarticKills810

end Max11DegreeRoutes
