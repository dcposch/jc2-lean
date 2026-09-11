import Grok810ScaleZeroQuarticMultiKills4Part03Scratch
import Grok810ScaleZeroQuarticMultiKills4Part05Scratch

/-! # Part 6 of `Grok810ScaleZeroQuarticMultiKills4Scratch`.

One declaration split out of `Grok810ScaleZeroQuarticMultiKills4Scratch`; statements are byte-identical.
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
theorem degreeZeroPrimitiveQuarticNoABDEF810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDEF810 A B C D E F G) :
    (degreeZeroPrimitiveQuarticNoABDEF810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      4 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
  have hC1 : C.natDegree + 1 ≤ 2 * A.natDegree := Nat.succ_le_of_lt hClt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroPrimitiveQuarticNoABDEF810_eq_polyOf]
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

theorem primitiveQuarticFaceABDEF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABDEF810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    : (primitiveQuarticFaceABDEF810 A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) =
      (1 / 65536 : k) * primitiveQuarticInnerABDEF810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
  simp only [primitiveQuarticFaceABDEF810, primitiveQuarticInnerABDEF810, coeff_add, coeff_sub, coeff_smul,
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
  have hdeg_A3DE : ((A ^ 3 * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 3 hAne) hDne, natDegree_pow]
    omega
  have hcf_A3DE : ((A ^ 3 * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A3DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2B2F : ((A ^ 2 * B ^ 2 * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne)) hFne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hBne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2B2F : ((A ^ 2 * B ^ 2 * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_A2B2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2BD2 : ((A ^ 2 * B * D ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hBne) (pow_ne_zero 2 hDne), natDegree_mul (pow_ne_zero 2 hAne) hBne, natDegree_pow, natDegree_pow]
    omega
  have hcf_A2BD2 : ((A ^ 2 * B * D ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_A2BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2EF : ((A ^ 2 * E * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hEne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hEne, natDegree_pow]
    omega
  have hcf_A2EF : ((A ^ 2 * E * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A2EF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
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
  have hdeg_ABDF : ((A * B * D * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hBne) hDne) hFne, natDegree_mul (mul_ne_zero hAne hBne) hDne, natDegree_mul hAne hBne]
    omega
  have hcf_ABDF : ((A * B * D * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * D.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_ABDF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_ABE2 : ((A * B * E ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hEne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABE2 : ((A * B * E ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_ABE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
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
  have hdeg_B2DE : ((B ^ 2 * D * E)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hBne) hDne) hEne, natDegree_mul (pow_ne_zero 2 hBne) hDne, natDegree_pow]
    omega
  have hcf_B2DE : ((B ^ 2 * D * E)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 2 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_B2DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BF2 : ((B * F ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hFne), natDegree_pow]
    omega
  have hcf_BF2 : ((B * F ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff * F.leadingCoeff ^ 2 := by
    rw [← hdeg_BF2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_D2F : ((D ^ 2 * F)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hFne, natDegree_pow]
    omega
  have hcf_D2F : ((D ^ 2 * F)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_D2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DE2 : ((D * E ^ 2)).natDegree = 4 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul hDne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_DE2 : ((D * E ^ 2)).coeff (4 * A.natDegree + 3 * B.natDegree) =
      D.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_DE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A4B3, hcf_A3B2D, hcf_A3DE, hcf_A2B2F, hcf_A2BD2, hcf_A2EF, hcf_AB5, hcf_AB3E, hcf_ABDF, hcf_ABE2, hcf_AD3, hcf_B4D, hcf_B2DE, hcf_BF2, hcf_D2F, hcf_DE2]
  ring

set_option maxHeartbeats 16000000 in
theorem quarticCone_ABDEF_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABDEF810 A B C D E F G)
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
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerABDEF810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoABDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceABDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_ABDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerABDEF810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoABDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceABDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + B.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ABDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerABDEF810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoABDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceABDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_ABDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerABDEF810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoABDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceABDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_ABDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerABDEF810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoABDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceABDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_ABDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerABDEF810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoABDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceABDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_ABDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveQuarticInnerABDEF810 A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveQuarticNoABDEF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := primitiveQuarticFaceABDEF810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hDne := hDne) (hEne := hEne) (hFne := hFne)
    have hz : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hBpos, hDpos, hEpos, hFpos, hAB, hAD, hAE, hAF, hClt, hGlt⟩
      omega
    rw [degreeZeroPrimitiveQuartic810_eq_ABDEF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 65536 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_ABDEF_identity A.leadingCoeff B.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff
  have hpow : E.leadingCoeff ^ 4 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : E.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hEne
  exact hlc ((pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hpow)

def kappaQuarticInnerABDEG810 (a b d e g : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d + 160 * b * g + 160 * d * e

def muQuarticInnerABDEG810 (a b d e g : k) : k :=
  (-80 : k) * a * d ^ 2 + 35 * b ^ 4 + (-240 : k) * b ^ 2 * e + 320 * e ^ 2

def nuQuarticInnerABDEG810 (a b d e g : k) : k :=
  (-5 : k) * a ^ 2 * b ^ 3 + 180 * a * b ^ 2 * d + (-160 : k) * a * b * g + (-160 : k) * a * d * e + (-480 : k) * b * d ^ 2 + 1280 * d * g

def xiQuarticInnerABDEG810 (a b d e g : k) : k :=
  (-15 : k) * a * b ^ 4 + 60 * a * b ^ 2 * e + 110 * b ^ 3 * d + (-160 : k) * b ^ 2 * g + (-400 : k) * b * d * e + 640 * e * g

def omicronQuarticInnerABDEG810 (a b d e g : k) : k :=
  (-5 : k) * a ^ 3 * b ^ 3 + (-180 : k) * a ^ 2 * b ^ 2 * d + (-160 : k) * a ^ 2 * b * g + (-160 : k) * a ^ 2 * d * e + 2240 * a * b * d ^ 2 + (-2560 : k) * a * d * g + (-336 : k) * b ^ 5 + 2560 * b ^ 3 * e + (-5120 : k) * b * e ^ 2 + (-2560 : k) * d ^ 3

end QuarticKills810

end Max11DegreeRoutes
