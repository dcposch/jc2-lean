import Grok810ScaleZeroQuarticMultiKillsPart40Scratch

/-! Part 41 of 47 of `Grok810ScaleZeroQuarticMultiKillsScratch`, split so that no single module elaborates them all
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


theorem omicronQuarticFaceBCF810_coeff_top
    {A B C D E F G : k[X]}
    (hcone : QuarticRatioConeBCF810 A B C D E F G)
    (hBne : B ≠ 0)
    (hCne : C ≠ 0)
    (hFne : F ≠ 0)
    : (omicronQuarticFaceBCF810 A B C D E F G).coeff (5 * B.natDegree) =
      (1 / 4096 : k) * omicronQuarticInnerBCF810 B.leadingCoeff C.leadingCoeff F.leadingCoeff := by
  rcases hcone with ⟨hBpos, hCpos, hFpos, hBC, hBF, hAlt, hDlt, hElt, hGlt⟩
  simp only [omicronQuarticFaceBCF810, omicronQuarticInnerBCF810, coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul]
  have hdeg_B5 : (B ^ 5).natDegree = 5 * B.natDegree := by
    rw [natDegree_pow]
  have hcf_B5 : (B ^ 5).coeff (5 * B.natDegree) =
      B.leadingCoeff ^ 5 := by
    rw [← hdeg_B5, coeff_natDegree, leadingCoeff_pow]
  have hdeg_BC3 : ((B * C ^ 3)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul hBne (pow_ne_zero 3 hCne), natDegree_pow]
    omega
  have hcf_BC3 : ((B * C ^ 3)).coeff (5 * B.natDegree) =
      B.leadingCoeff * C.leadingCoeff ^ 3 := by
    rw [← hdeg_BC3, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  have hdeg_C2F : ((C ^ 2 * F)).natDegree = 5 * B.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 hCne) hFne, natDegree_pow]
    omega
  have hcf_C2F : ((C ^ 2 * F)).coeff (5 * B.natDegree) =
      C.leadingCoeff ^ 2 * F.leadingCoeff := by
    rw [← hdeg_C2F, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow]
  rw [hcf_B5, hcf_BC3, hcf_C2F]
  ring


set_option maxHeartbeats 16000000 in
theorem quarticCone_BCF_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hcone : QuarticRatioConeBCF810 A B C D E F G)
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
    rcases hcone with ⟨hBpos, hCpos, hFpos, hBC, hBF, hAlt, hDlt, hElt, hGlt⟩
    omega
  have hCne : C ≠ 0 := by
    intro h0
    have : C.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hFpos, hBC, hBF, hAlt, hDlt, hElt, hGlt⟩
    omega
  have hFne : F ≠ 0 := by
    intro h0
    have : F.natDegree = 0 := by simp [h0]
    rcases hcone with ⟨hBpos, hCpos, hFpos, hBC, hBF, hAlt, hDlt, hElt, hGlt⟩
    omega
  have hprimdeg :
      (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G).natDegree =
        1 :=
    natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t) hjdiv hder
  have hkappainner : kappaQuarticInnerBCF810 B.leadingCoeff C.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroKappaQuarticNoBCF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := kappaQuarticFaceBCF810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hFne := hFne)
    have hz : (degreeZeroKappaQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (B.natDegree + 2 * C.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hkap]
      rcases hcone with ⟨hBpos, hCpos, hFpos, hBC, hBF, hAlt, hDlt, hElt, hGlt⟩
      omega
    rw [degreeZeroKappaQuartic810_eq_BCF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 128 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hmuinner : muQuarticInnerBCF810 B.leadingCoeff C.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroMuQuarticNoBCF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := muQuarticFaceBCF810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hFne := hFne)
    have hz : (degreeZeroMuQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (4 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hmu]
      rcases hcone with ⟨hBpos, hCpos, hFpos, hBC, hBF, hAlt, hDlt, hElt, hGlt⟩
      omega
    rw [degreeZeroMuQuartic810_eq_BCF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 2048 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have homicroninner : omicronQuarticInnerBCF810 B.leadingCoeff C.leadingCoeff F.leadingCoeff = 0 := by
    have hrest := degreeZeroOmicronQuarticNoBCF810_natDegree_lt l beta gamma delta epsilon zeta eta theta
        A B C D E F G hcone
    have hct := omicronQuarticFaceBCF810_coeff_top (hcone := hcone) (hBne := hBne) (hCne := hCne) (hFne := hFne)
    have hz : (degreeZeroOmicronQuartic810 l beta gamma delta epsilon zeta eta theta
        A B C D E F G).coeff (5 * B.natDegree) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [homi]
      rcases hcone with ⟨hBpos, hCpos, hFpos, hBC, hBF, hAlt, hDlt, hElt, hGlt⟩
      omega
    rw [degreeZeroOmicronQuartic810_eq_BCF_add_rest, coeff_add,
        coeff_eq_zero_of_natDegree_lt hrest, add_zero] at hz
    have hden : (1 / 4096 : k) ≠ 0 :=
      div_ne_zero (by norm_num) (by norm_num)
    have hmul := mul_eq_zero.mp (hct.symm.trans hz)
    rcases hmul with h | h
    · exact (hden h).elim
    · exact h
  have hid := quarticInner_BCF_identity B.leadingCoeff C.leadingCoeff F.leadingCoeff
  have hpow : B.leadingCoeff ^ 5 = 0 := by
    rw [hkappainner, hmuinner, homicroninner] at hid
    simpa using hid.symm
  have hlc : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hBne
  exact hlc ((pow_eq_zero_iff (by decide : (5 : ℕ) ≠ 0)).mp hpow)



def muQuarticInnerCEG810 (c e g : k) : k :=
  (-5 : k) * c ^ 3 + 40 * c * g + 20 * e ^ 2


def xiQuarticInnerCEG810 (c e g : k) : k :=
  (-15 : k) * c ^ 2 * e + 40 * e * g


end QuarticKills810
end Max11DegreeRoutes
end
