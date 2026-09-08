import Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegSplitPart14Scratch

/-! # SPEED: theorems of `Grok810ScaleZeroQuarticMultiKills7SpeedReflValDegScratch`, part 15 of 24, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open scoped Polynomial.Bivariate
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
set_option maxRecDepth 8000000

section QuarticKills810

variable {k : Type*} [Field k] [CharZero k]

theorem primitiveQuarticFaceACDEFG810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeACDEFG810 A B C D E F G)
    (hAne : A ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    (hEne : E ≠ 0)
    (hFne : F ≠ 0)
    (hGne : G ≠ 0)
    : (primitiveQuarticFaceACDEFG810 A B C D E F G).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      (1 / 2048 : k) * primitiveQuarticInnerACDEFG810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff := by
  rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
  simp only [primitiveQuarticFaceACDEFG810, primitiveQuarticInnerACDEFG810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A3CF : ((A ^ 3 * C * F)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hCne) hFne, natDegree_mul (pow_ne_zero 3 hAne) hCne, natDegree_pow]
  have hcf_A3CF : ((A ^ 3 * C * F)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff ^ 3 * C.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A3CF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A3DE : ((A ^ 3 * D * E)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 3 hAne) hDne) hEne, natDegree_mul (pow_ne_zero 3 hAne) hDne, natDegree_pow]
    omega
  have hcf_A3DE : ((A ^ 3 * D * E)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff ^ 3 * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_A3DE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2C2D : ((A ^ 2 * C ^ 2 * D)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne)) hDne, natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 2 hCne), natDegree_pow, natDegree_pow]
    omega
  have hcf_A2C2D : ((A ^ 2 * C ^ 2 * D)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff ^ 2 * C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_A2C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_A2DG : ((A ^ 2 * D * G)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hDne) hGne, natDegree_mul (pow_ne_zero 2 hAne) hDne, natDegree_pow]
    omega
  have hcf_A2DG : ((A ^ 2 * D * G)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff ^ 2 * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_A2DG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_A2EF : ((A ^ 2 * E * F)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (pow_ne_zero 2 hAne) hEne) hFne, natDegree_mul (pow_ne_zero 2 hAne) hEne, natDegree_pow]
    omega
  have hcf_A2EF : ((A ^ 2 * E * F)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff ^ 2 * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_A2EF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_ACDE : ((A * C * D * E)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero hAne hCne) hDne) hEne, natDegree_mul (mul_ne_zero hAne hCne) hDne, natDegree_mul hAne hCne]
    omega
  have hcf_ACDE : ((A * C * D * E)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * C.leadingCoeff * D.leadingCoeff * E.leadingCoeff := by
    rw [← hdeg_ACDE, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_AD3 : ((A * D ^ 3)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul hAne (pow_ne_zero 3 hDne), natDegree_pow]
    omega
  have hcf_AD3 : ((A * D ^ 3)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * D.leadingCoeff ^ 3 := by
    rw [← hdeg_AD3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_AFG : ((A * F * G)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hFne) hGne, natDegree_mul hAne hFne]
    omega
  have hcf_AFG : ((A * F * G)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      A.leadingCoeff * F.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_AFG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_C3D : ((C ^ 3 * D)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hCne) hDne, natDegree_pow]
    omega
  have hcf_C3D : ((C ^ 3 * D)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      C.leadingCoeff ^ 3 * D.leadingCoeff := by
    rw [← hdeg_C3D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_CDG : ((C * D * G)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hDne) hGne, natDegree_mul hCne hDne]
    omega
  have hcf_CDG : ((C * D * G)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      C.leadingCoeff * D.leadingCoeff * G.leadingCoeff := by
    rw [← hdeg_CDG, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_CEF : ((C * E * F)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (mul_ne_zero hCne hEne) hFne, natDegree_mul hCne hEne]
    omega
  have hcf_CEF : ((C * E * F)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      C.leadingCoeff * E.leadingCoeff * F.leadingCoeff := by
    rw [← hdeg_CEF, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul]
  have hdeg_D2F : ((D ^ 2 * F)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hDne) hFne, natDegree_pow]
    omega
  have hcf_D2F : ((D ^ 2 * F)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      D.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_D2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_DE2 : ((D * E ^ 2)).natDegree = 3 * A.natDegree + C.natDegree + F.natDegree := by
    rw [natDegree_mul hDne (pow_ne_zero 2 hEne), natDegree_pow]
    omega
  have hcf_DE2 : ((D * E ^ 2)).coeff (3 * A.natDegree + C.natDegree + F.natDegree) =
      D.leadingCoeff * E.leadingCoeff ^ 2 := by
    rw [← hdeg_DE2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A3CF, hcf_A3DE, hcf_A2C2D, hcf_A2DG, hcf_A2EF, hcf_ACDE, hcf_AD3, hcf_AFG, hcf_C3D, hcf_CDG, hcf_CEF, hcf_D2F, hcf_DE2]
  ring


set_option maxHeartbeats 16000000 in
theorem quarticCone_ACDEFG_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeACDEFG810 A B C D E F G)
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
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
    omega
  have hEne : E ≠ 0 := by
    intro h0
    have : E.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
    omega
  have hGne : G ≠ 0 := by
    intro h0
    have : G.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerACDEFG810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoACDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceACDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (C.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_ACDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 16 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerACDEFG810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoACDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceACDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 2 * D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ACDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerACDEFG810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoACDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceACDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + C.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_ACDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hxiinner : xiQuarticInnerACDEFG810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroXiQuarticNoACDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := xiQuarticFaceACDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroXiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + D.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hxi]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
      omega
    rw [degreeZeroXiQuartic810_eq_ACDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerACDEFG810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoACDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceACDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + C.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_ACDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hpiinner : piQuarticInnerACDEFG810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPiQuarticNoACDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := piQuarticFaceACDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPiQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + C.natDegree + 2 * D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hpi]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
      omega
    rw [degreeZeroPiQuartic810_eq_ACDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 256 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hprimitiveinner : primitiveQuarticInnerACDEFG810 A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff = 0 := by
    have hrest := degreeZeroPrimitiveQuarticNoACDEFG810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := primitiveQuarticFaceACDEFG810_coeff_top (hcone := hcone) (hAne := hAne) (hCne := hCne) (hDne := hDne) (hEne := hEne) (hFne := hFne) (hGne := hGne)
    have hz : (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * A.natDegree + C.natDegree + F.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hprimdeg]
      rcases hcone with ⟨hApos, hCpos, hDpos, hEpos, hFpos, hGpos, hAC, hAD, hAE, hAF, hAG, hBlt⟩
      omega
    rw [degreeZeroPrimitiveQuartic810_eq_ACDEFG_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_ACDEFG_identity A.leadingCoeff C.leadingCoeff D.leadingCoeff E.leadingCoeff F.leadingCoeff G.leadingCoeff
  have hpow : F.leadingCoeff ^ 3 = 0 := by
    rw [hkappainner, hmuinner, hnuinner, hxiinner, homicroninner, hpiinner, hprimitiveinner] at hid
    simpa using hid.symm
  have hlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hFne
  exact hlc ((pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hpow)



set_option maxHeartbeats 64000000 in
theorem quarticInner_BCDEFG_identity
    (b c d e f g : k) :
    ((14533936594203623741610001 / 278906863202631497706048000 : k) * b ^ 4 * c * g + (211658868460441050608515009 / 1487503270414034654432256000 : k) * b ^ 4 * d * f + (9110643028543264575815521 / 1673441179215788986236288000 : k) * b ^ 4 * e ^ 2 + (-3590840358223574535940378559 / 13387529433726311889890304000 : k) * b ^ 3 * c ^ 2 * f + (30635097007401134648676301 / 133875294337263118898903040 : k) * b ^ 3 * c * d * e + (104156522792405025045232823 / 892501962248420792659353600 : k) * b ^ 3 * d ^ 3 + (49584174133602208296462589 / 61979302933918110601344000 : k) * b ^ 3 * f * g + (824733890494050273385285447 / 1561878433934736387153868800 : k) * b ^ 2 * c ^ 3 * e + (-920146983676456879094907632767 / 291550641001150792268722176000 : k) * b ^ 2 * c ^ 2 * d ^ 2 + (-666946136078318861354129923 / 325391340403070080657056000 : k) * b ^ 2 * c * e * g + (42302092642692323612703582691 / 109331490375431547100770816000 : k) * b ^ 2 * c * f ^ 2 + (1109220248445956465109438349 / 9939226397766504281888256000 : k) * b ^ 2 * d ^ 2 * g + (-1930706557436915325324104371 / 1561878433934736387153868800 : k) * b ^ 2 * d * e * f + (-36727779818137792270693573 / 976174021209210241971168000 : k) * b ^ 2 * e ^ 3 + (-37486519406751048976679435939 / 54665745187715773550385408000 : k) * b * c ^ 4 * d + (-18321240003281031540772733 / 12796288667536463846064000 : k) * b * c ^ 2 * d * g + (-1871034025361925456644627 / 7335714598458906810304000 : k) * b * c ^ 2 * e * f + (23909323838334206758977095519 / 6073971687523974838931712000 : k) * b * c * d ^ 2 * f + (-1423661011685974661925503503 / 1518492921880993709732928000 : k) * b * c * d * e ^ 2 + (-43021498970372860552543213 / 69022405540045168624224000 : k) * b * d ^ 3 * e + (-6247161910111917289437862399 / 2562456805674176885174316000 : k) * b * d * g ^ 2 + (-2107316604412179846653275097 / 1281228402837088442587158000 : k) * b * e * f * g + (-38545974226275579380549359 / 142358711426343160287462000 : k) * b * f ^ 3 + (13205372864421369659094581 / 202841355056459271058944000 : k) * c ^ 6 + (-2217292732343994430592065757 / 1464261031813815362956752000 : k) * c ^ 4 * g + (214019727318442159004340731 / 218662980750863094201541632 : k) * c ^ 3 * d * f + (-367207737287786141504499139 / 372720989916243910570809600 : k) * c ^ 3 * e ^ 2 + (101587425537464900635115760611 / 54665745187715773550385408000 : k) * c ^ 2 * d ^ 2 * e + (5495745791272630604085179657 / 732130515906907681478376000 : k) * c ^ 2 * g ^ 2 + (2945251735086032707746129799 / 4555478765642981129198784000 : k) * c * d ^ 4 + (58108289581969856677270253 / 19980170024749917233328000 : k) * c * d * f * g + (1412945956185109832771275717 / 284717422852686320574924000 : k) * c * e ^ 2 * g + (31721799448751661627952171 / 512491361134835377034863200 : k) * c * e * f ^ 2 + (57107219444446029531814677859 / 20499654445393415081394528000 : k) * d ^ 2 * e * g + (5008411475162274382184487101 / 6833218148464471693798176000 : k) * d ^ 2 * f ^ 2 + (848400052771680063707180437 / 284717422852686320574924000 : k) * d * e ^ 2 * f + (-7399396804754860771226587 / 366065257953453840739188000 : k) * e ^ 4 + (-1578284065480694762 / 2257956074875858245 : k) * g ^ 3) * kappaQuarticInnerBCDEFG810 b c d e f g +
      ((5477543471490589609100071 / 488087010604605120985584000 : k) * b ^ 2 * c * e * f + (13205372864421369659094581 / 2975006540828069308864512000 : k) * b * c ^ 5 + (169092095663645409842640881 / 1301565361612280322628224000 : k) * b * c ^ 3 * g + (315305434354883462462984509 / 5206261446449121290512896000 : k) * b * c ^ 2 * d * f + (-2512737961696442500416019 / 289236747024951182806272000 : k) * b * c ^ 2 * e ^ 2 + (604453382644572158906382397 / 3123756867869472774307737600 : k) * b * c * d ^ 2 * e + (-164995254877300133144292179 / 418360294803947246559072000 : k) * b * c * g ^ 2 + (104156522792405025045232823 / 2082504578579648516205158400 : k) * b * d ^ 4 + (46026947828586822651572167 / 162695670201535040328528000 : k) * b * d * f * g + (-11826145523491396192401989 / 418360294803947246559072000 : k) * b * e ^ 2 * g + (-2090712766509378650652451 / 68503440084856859085696000 : k) * b * e * f ^ 2 + (159451312052709508543045679 / 31237568678694727743077376000 : k) * c ^ 4 * f + (17997348231306529218266299 / 283977897079042979482521600 : k) * c ^ 3 * d * e + (109577771260248740274934429 / 624751373573894554861547520 : k) * c ^ 2 * d ^ 3 + (-1642022635032075972609533503 / 5857044127255261451827008000 : k) * c ^ 2 * f * g + (-735041734017685662534941621 / 1171408825451052290365401600 : k) * c * d * e * g + (-69173529453971304589942223 / 278906863202631497706048000 : k) * c * d * f ^ 2 + (174994919909803895061541 / 11575186022243599707168000 : k) * c * e ^ 2 * f + (-19858435876479377593401943 / 130156536161228032262822400 : k) * d ^ 3 * g + (-950992762329657011606194219 / 3904696084836840967884672000 : k) * d ^ 2 * e * f + (7509015333825085353748687 / 2928522063627630725913504000 : k) * d * e ^ 3 + (-100207594989822229956445241 / 488087010604605120985584000 : k) * f * g ^ 2) * muQuarticInnerBCDEFG810 b c d e f g +
      ((-9110643028543264575815521 / 1115627452810525990824192000 : k) * b ^ 3 * e * f + (-201696017073639102215578417 / 1301565361612280322628224000 : k) * b ^ 2 * c ^ 2 * g + (-2237696366587541620417 / 518965455188309538528000 : k) * b ^ 2 * c * e ^ 2 + (142440423655866458022673721 / 292852206362763072591350400 : k) * b ^ 2 * g ^ 2 + (-565480876600038522143340829 / 5206261446449121290512896000 : k) * b * c ^ 3 * f + (1867740696719074778690181439 / 18221915062571924516795136000 : k) * b * c ^ 2 * d * e + (-12049732732455999485279702729 / 18221915062571924516795136000 : k) * b * c * d ^ 3 + (27659236405206997000223090021 / 40999308890786830162789056000 : k) * b * c * f * g + (-71611811848235676280326317 / 2928522063627630725913504000 : k) * b * d * e * g + (4632508993972713496551353 / 103533608310067752936336000 : k) * b * d * f ^ 2 + (54314680688163366435719537 / 976174021209210241971168000 : k) * b * e ^ 2 * f + (2442213083123145524272077409 / 27332872593857886775192704000 : k) * c ^ 4 * e + (106376243450011157029276217 / 19878452795533008563776512000 : k) * c ^ 3 * d ^ 2 + (-548148568928734435105436777 / 854152268558058961724772000 : k) * c ^ 2 * e * g + (781171440695101037186320069 / 7454419798324878211416192000 : k) * c ^ 2 * f ^ 2 + (943255251774429799031283101 / 1438572241781994040799616000 : k) * c * d ^ 2 * g + (-354503718217253322927509231 / 1782578647425514354903872000 : k) * c * d * e * f + (-812741547996775807411741 / 48808701060460512098558400 : k) * c * e ^ 3 + (69809439958895683421049589 / 86771024107485354841881600 : k) * d ^ 3 * f + (-1704079397817837241042953953 / 10249827222696707540697264000 : k) * d ^ 2 * e ^ 2 + (61262001885092548547193161 / 427076134279029480862386000 : k) * e * g ^ 2 + (-20162729059552434442071317 / 106769033569757370215596500 : k) * f ^ 2 * g) * nuQuarticInnerBCDEFG810 b c d e f g +
      ((9110643028543264575815521 / 1115627452810525990824192000 : k) * b ^ 3 * e ^ 2 + (270433591520835699148437139 / 5206261446449121290512896000 : k) * b * c ^ 3 * e + (-39831043415363059908587090567 / 72887660250287698067180544000 : k) * b * c ^ 2 * d ^ 2 + (-389184314646322086651027131 / 1952348042418420483942336000 : k) * b * c * e * g + (296819277551038936160976469 / 9110957531285962258397568000 : k) * b * c * f ^ 2 + (138648536539707993851236613 / 2484806599441626070472064000 : k) * b * d ^ 2 * g + (164931306360628672583974141 / 1952348042418420483942336000 : k) * b * d * e * f + (-7227818931072657381082049 / 195234804241842048394233600 : k) * b * e ^ 3 + (-3393486313211190378596467357 / 27332872593857886775192704000 : k) * c ^ 4 * d + (71855307294798157741721851 / 85415226855805896172477200 : k) * c ^ 2 * d * g + (-7010861718405018496313339273 / 27332872593857886775192704000 : k) * c ^ 2 * e * f + (9825786882946012028414755429 / 13666436296928943387596352000 : k) * c * d ^ 2 * f + (-193572857185390333062816689 / 1366643629692894338759635200 : k) * c * d * e ^ 2 + (21258211170819076891775831 / 1188385764950342903269248000 : k) * d ^ 3 * e + (-41267718962830353432410899 / 142358711426343160287462000 : k) * d * g ^ 2 + (1355078694208483236436836989 / 3416609074232235846899088000 : k) * e * f * g + (1 / 160 : k) * f ^ 3) * xiQuarticInnerBCDEFG810 b c d e f g +
      ((-14533936594203623741610001 / 390469608483684096788467200 : k) * b * c * d * g + (2651799371560731301654721 / 520626144644912129051289600 : k) * b * c * e * f + (-211658868460441050608515009 / 2082504578579648516205158400 : k) * b * d ^ 2 * f + (9110643028543264575815521 / 520626144644912129051289600 : k) * b * d * e ^ 2 + (13205372864421369659094581 / 1785003924496841585318707200 : k) * c ^ 5 + (-30835897299200469928078769 / 390469608483684096788467200 : k) * c ^ 3 * g + (29547678844033444372781039 / 312375686786947277430773760 : k) * c ^ 2 * d * f + (3058748979135449651820619 / 223125490562105198164838400 : k) * c ^ 2 * e ^ 2 + (95750169172800571585360603 / 446250981124210396329676800 : k) * c * d ^ 2 * e + (20885498996724416070349241 / 195234804241842048394233600 : k) * c * g ^ 2 + (11134740323892979762744087 / 65078268080614016131411200 : k) * d * f * g + (-4415762621430104875928741 / 65078268080614016131411200 : k) * e ^ 2 * g + (-3071750929513095030109361 / 111562745281052599082419200 : k) * e * f ^ 2) * omicronQuarticInnerBCDEFG810 b c d e f g +
      ((633736803920961795250979 / 10968247429316969010912000 : k) * b * c * d * f + (-7015526683765970256479 / 2742061857329242252728000 : k) * b * c * e ^ 2 + (-11070852267960672905909 / 332371134221726333664000 : k) * b * d ^ 2 * e + (789142032740347381 / 9031824299503432980 : k) * b * g ^ 2 + (62746911986666592630509 / 5484123714658484505456000 : k) * c ^ 3 * f + (-76650453249095878041763 / 997113402665179000992000 : k) * c ^ 2 * d * e + (-10396264629108088880803 / 156689248990242414441600 : k) * c * d ^ 3 + (48042228617015258365931 / 685515464332310563182000 : k) * c * f * g + (418899805340272970071871 / 1371030928664621126364000 : k) * d * e * g + (-5242234958677159734437 / 152336769851624569596000 : k) * d * f ^ 2 + (5745709004860393863271 / 685515464332310563182000 : k) * e ^ 2 * f) * piQuarticInnerBCDEFG810 b c d e f g +
      ((106409323842297610183 / 15638381185770782883840 : k) * c ^ 2 * d ^ 2 + (-43787641556907155 / 647896947800636128 : k) * c * e * g + (-440534669012465899661 / 41050750612648305070080 : k) * c * f ^ 2 + (6783105594638405525 / 1172878588932808716288 : k) * d ^ 2 * g + (68461370571137745217 / 2932196472332021790720 : k) * d * e * f + (3429877098183179 / 183262279520751361920 : k) * e ^ 3) * primitiveQuarticInnerBCDEFG810 b c d e f g =
      f ^ 5 := by
  simp only [kappaQuarticInnerBCDEFG810, muQuarticInnerBCDEFG810, nuQuarticInnerBCDEFG810, xiQuarticInnerBCDEFG810, omicronQuarticInnerBCDEFG810, piQuarticInnerBCDEFG810, primitiveQuarticInnerBCDEFG810]
  ring


set_option maxHeartbeats 16000000 in
theorem degreeZeroKappaQuartic810_eq_BCDEFG_add_rest
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X]) :
    degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta A B C D E F G =
      kappaQuarticFaceBCDEFG810 A B C D E F G +
        degreeZeroKappaQuarticNoBCDEFG810 l beta gamma delta epsilon zeta eta theta
          A B C D E F G := by
  simp only [Max11ReflectDeg.polyOf_cons, Max11ReflectDeg.polyOf_nil_left, Max11ReflectDeg.polyOf_nil_right, Max11ReflectDeg.mono_cons, Max11ReflectDeg.mono_nil_left, Max11ReflectDeg.mono_nil_right, pow_zero, pow_one, mul_one, one_mul, add_zero, mul_assoc, degreeZeroKappaQuartic810, kappaQuarticFaceBCDEFG810, degreeZeroKappaQuarticNoBCDEFG810]
  all_goals module


end QuarticKills810

end Max11DegreeRoutes

end
