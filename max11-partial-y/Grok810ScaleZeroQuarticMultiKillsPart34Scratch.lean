import Grok810ScaleZeroQuarticMultiKillsPart29Scratch
import Grok810ScaleZeroQuarticMultiKillsPart32Scratch
import Grok810ScaleZeroQuarticMultiKillsPart33Scratch

/-! Part 34 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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
theorem degreeZeroNuQuarticNoBCD810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCD810 A B C D E F G) :
    (degreeZeroNuQuarticNoBCD810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      3 * B.natDegree + C.natDegree := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt, hFlt, hGlt⟩
  have hA1 : 3 * A.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hAlt
  have hE1 : E.natDegree + 1 ≤ 2 * B.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 3 * F.natDegree + 1 ≤ 7 * B.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : 3 * G.natDegree + 1 ≤ 8 * B.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroNuQuarticNoBCD810_eq_polyOf]
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


theorem nuQuarticFaceBCD810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCD810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hDne : D ≠ 0)
    : (nuQuarticFaceBCD810 A B C D E F G).coeff (3 * B.natDegree + C.natDegree) =
      (1 / 512 : k) * nuQuarticInnerBCD810 B.leadingCoeff C.leadingCoeff D.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt, hFlt, hGlt⟩
  simp only [nuQuarticFaceBCD810, nuQuarticInnerBCD810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
  have hcf_B3C : ((B ^ 3 * C)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_BD2 : ((B * D ^ 2)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 2 hDne), natDegree_pow]
    omega
  have hcf_BD2 : ((B * D ^ 2)).coeff (3 * B.natDegree + C.natDegree) =
      B.leadingCoeff * D.leadingCoeff ^ 2 := by
    rw [← hdeg_BD2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2D : ((C ^ 2 * D)).natDegree = 3 * B.natDegree + C.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hDne, natDegree_pow]
    omega
  have hcf_C2D : ((C ^ 2 * D)).coeff (3 * B.natDegree + C.natDegree) =
      C.leadingCoeff ^ 2 * D.leadingCoeff := by
    rw [← hdeg_C2D, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B3C, hcf_BD2, hcf_C2D]
  ring


set_option maxHeartbeats 16000000 in
theorem quarticCone_BCD_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCD810 A B C D E F G)
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
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt, hFlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt, hFlt, hGlt⟩
    omega
  have hDne : D ≠ 0 := by
    intro h0
    have : D.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt, hFlt, hGlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerBCD810 B.leadingCoeff C.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoBCD810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceBCD810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * B.natDegree + D.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt, hFlt, hGlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_BCD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerBCD810 B.leadingCoeff C.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoBCD810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceBCD810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt, hFlt, hGlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_BCD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerBCD810 B.leadingCoeff C.leadingCoeff D.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoBCD810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceBCD810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hDne := hDne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (3 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hBpos, hCpos, hDpos, hBC, hBD, hAlt, hElt, hFlt, hGlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_BCD_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_BCD_identity B.leadingCoeff C.leadingCoeff D.leadingCoeff
  have hpow : B.leadingCoeff ^ 7 = 0 := by
    rw [hkappainner, hmuinner, hnuinner] at hid
    simpa using hid.symm
  have hlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  exact hlc ((pow_eq_zero_iff (by decide : (7 : ℕ) ≠ 0)).mp hpow)



def kappaQuarticInnerBCF810 (b c f : k) : k :=
  (-15 : k) * b * c ^ 2 + 40 * c * f


end QuarticKills810
end Max11DegreeRoutes
end
