import Grok810ScaleZeroQuarticMultiKillsPart14Scratch

/-! Part 15 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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
theorem degreeZeroNuQuarticNoABC810_natDegree_lt
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABC810 A B C D E F G) :
    (degreeZeroNuQuarticNoABC810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).natDegree <
      2 * A.natDegree + 3 * B.natDegree := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt, hFlt, hGlt⟩
  have hD1 : 2 * D.natDegree + 1 ≤ 5 * A.natDegree := Nat.succ_le_of_lt hDlt
  have hE1 : E.natDegree + 1 ≤ 3 * A.natDegree := Nat.succ_le_of_lt hElt
  have hF1 : 2 * F.natDegree + 1 ≤ 7 * A.natDegree := Nat.succ_le_of_lt hFlt
  have hG1 : G.natDegree + 1 ≤ 4 * A.natDegree := Nat.succ_le_of_lt hGlt
  rw [speedRefl_degreeZeroNuQuarticNoABC810_eq_polyOf]
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


theorem nuQuarticFaceABC810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeABC810 A B C D E F G)
    (hAne : A ≠ 0)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    : (nuQuarticFaceABC810 A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) =
      (1 / 4096 : k) * nuQuarticInnerABC810 A.leadingCoeff B.leadingCoeff C.leadingCoeff := by
  rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt, hFlt, hGlt⟩
  simp only [nuQuarticFaceABC810, nuQuarticInnerABC810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_A2B3 : ((A ^ 2 * B ^ 3)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hAne) (pow_ne_zero 3 hBne), natDegree_pow, natDegree_pow]
  have hcf_A2B3 : ((A ^ 2 * B ^ 3)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff ^ 2 * B.leadingCoeff ^ 3 := by
    rw [← hdeg_A2B3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow]
  have hdeg_ABC2 : ((A * B * C ^ 2)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (mul_ne_zero hAne hBne) (pow_ne_zero 2 hCne), natDegree_mul hAne hBne, natDegree_pow]
    omega
  have hcf_ABC2 : ((A * B * C ^ 2)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      A.leadingCoeff * B.leadingCoeff * C.leadingCoeff ^ 2 := by
    rw [← hdeg_ABC2, coeff_natDegree, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_B3C : ((B ^ 3 * C)).natDegree = 2 * A.natDegree + 3 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 3 hBne) hCne, natDegree_pow]
    omega
  have hcf_B3C : ((B ^ 3 * C)).coeff (2 * A.natDegree + 3 * B.natDegree) =
      B.leadingCoeff ^ 3 * C.leadingCoeff := by
    rw [← hdeg_B3C, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_A2B3, hcf_ABC2, hcf_B3C]
  ring


set_option maxHeartbeats 16000000 in
theorem quarticCone_ABC_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeABC810 A B C D E F G)
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
    rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hBne : B ≠ 0 := by
    intro h0
    have : B.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt, hFlt, hGlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerABC810 A.leadingCoeff B.leadingCoeff C.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoABC810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceABC810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt, hFlt, hGlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_ABC_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 512 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerABC810 A.leadingCoeff B.leadingCoeff C.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoABC810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceABC810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (A.natDegree + 2 * B.natDegree + C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt, hFlt, hGlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_ABC_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hnuinner : nuQuarticInnerABC810 A.leadingCoeff B.leadingCoeff C.leadingCoeff = 0 := by
    have hrest := degreeZeroNuQuarticNoABC810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := nuQuarticFaceABC810_coeff_top (hcone := hcone) (hAne := hAne) (hBne := hBne) (hCne := hCne)
    have hz : (degreeZeroNuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (2 * A.natDegree + 3 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hnu]
      rcases hcone with ⟨hApos, hBpos, hCpos, hAB, hAC, hDlt, hElt, hFlt, hGlt⟩
      omega
    rw [degreeZeroNuQuartic810_eq_ABC_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_ABC_identity A.leadingCoeff B.leadingCoeff C.leadingCoeff
  have hpow : C.leadingCoeff ^ 5 = 0 := by
    rw [hkappainner, hmuinner, hnuinner] at hid
    simpa using hid.symm
  have hlc : C.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hCne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)



def kappaQuarticInnerABD810 (a b d : k) : k :=
  5 * a * b ^ 3 + (-60 : k) * b ^ 2 * d


end QuarticKills810
end Max11DegreeRoutes
end
