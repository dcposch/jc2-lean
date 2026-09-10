import Grok810ScaleZeroQuarticSigmaLadderPart58Scratch

/-! Part 59 of 95 of `Grok810ScaleZeroQuarticSigmaLadderScratch`, split so that no single module elaborates them all
at once.  Statements are unchanged. -/

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

section QuarticSigmaCorners810


set_option maxHeartbeats 64000000 in
theorem primitiveQuartic_of_lettersZero
    (l beta gamma delta epsilon zeta eta theta : k)
    (A : k[X]) :
    degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta eta
        theta A 0 0 0 0 0 0 =
      (1575 / 268435456 * l : k) • A ^ 8 +
        (25 / 1048576 * beta : k) • A ^ 7 +
        (25 / 262144 * delta : k) • A ^ 6 +
        (3 / 8192 * zeta : k) • A ^ 5 +
        (5 / 4096 * theta : k) • A ^ 4 := by
  simp only [degreeZeroPrimitiveQuartic810, rhoBaseGroupQuartic810,
    rhoBetaGroupQuartic810, rhoGammaGroupQuartic810,
    rhoDeltaGroupQuartic810, rhoEpsilonGroupQuartic810,
    rhoZetaGroupQuartic810, rhoEtaGroupQuartic810,
    rhoThetaGroupQuartic810]
  have hpow2 : (0 : k[X]) ^ 2 = 0 := zero_pow (by decide)
  have hpow3 : (0 : k[X]) ^ 3 = 0 := zero_pow (by decide)
  have hpow4 : (0 : k[X]) ^ 4 = 0 := zero_pow (by decide)
  have hpow5 : (0 : k[X]) ^ 5 = 0 := zero_pow (by decide)
  apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
  simp only [Polynomial.smul_eq_C_mul, map_add, map_sub, map_mul,
    map_pow, map_neg, map_zero, RatFunc.algebraMap_C, map_div₀,
    map_ofNat, map_natCast, map_one]
  simp only [hpow2, hpow3, hpow4, hpow5,
    zero_mul, mul_zero, zero_smul, smul_zero, add_zero, zero_add,
    sub_zero, neg_zero, sub_self]
  ring


theorem quarticADominant_allLettersZero_impossible
    {j t : k}
    (l beta gamma delta epsilon zeta eta theta : k)
    (A B C D E F G : k[X])
    (hApos : 0 < A.natDegree)
    (hB : B = 0) (hC : C = 0) (hD : D = 0)
    (hE : E = 0) (hF : F = 0) (hG : G = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveQuartic810 l beta gamma delta epsilon zeta
          eta theta A B C D E F G) =
        Polynomial.C (j / t)) :
    False := by
  have hBn : B.natDegree = 0 := by simp [hB]
  have hCn : C.natDegree = 0 := by simp [hC]
  have hDn : D.natDegree = 0 := by simp [hD]
  have hEn : E.natDegree = 0 := by simp [hE]
  have hFn : F.natDegree = 0 := by simp [hF]
  have hGn : G.natDegree = 0 := by simp [hG]
  by_cases hl0 : l = 0
  · by_cases hb0 : beta = 0
    · by_cases hd0 : delta = 0
      · by_cases hz0 : zeta = 0
        · have hP := primitiveQuartic_of_lettersZero l beta gamma delta
            epsilon zeta eta theta A
          rw [hB, hC, hD, hE, hF, hG, hP] at hder
          by_cases ht0 : theta = 0
          · simp only [hl0, hb0, hd0, hz0, ht0, mul_zero, zero_smul,
              add_zero] at hder
            have : derivative (0 : k[X]) = Polynomial.C (j / t) := hder
            rw [derivative_zero] at this
            exact hjdiv (C_eq_zero.mp this.symm)
          · have hdeg :=
              natDegree_eq_one_of_derivative_eq_nonzero_C810 _ (j / t)
                hjdiv hder
            have hAne : A ≠ 0 := by
              intro h0
              have : A.natDegree = 0 := by simp [h0]
              omega
            have hc : (5 / 4096 * theta : k) ≠ 0 :=
              mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) ht0
            have hlead :
                ((5 / 4096 * theta : k) • A ^ 4).natDegree =
                  4 * A.natDegree := by
              rw [natDegree_smul _ hc, natDegree_pow]
            simp only [hl0, hb0, hd0, hz0, mul_zero, zero_smul,
              add_zero, zero_add] at hdeg
            rw [hlead] at hdeg
            omega
        · exact quarticADominant_constantLetters_impossible_of_zeta
            (j := j) (t := t) gamma epsilon zeta eta theta A B C D E F G
            hApos hBn hCn hDn hEn hFn hGn hz0 hjdiv
            (by simpa [hl0, hb0, hd0] using hder)
      · exact quarticADominant_constantLetters_impossible_of_delta
          (j := j) (t := t) gamma delta epsilon zeta eta theta A B C D E
          F G hApos hBn hCn hDn hEn hFn hGn hd0 hjdiv
          (by simpa [hl0, hb0] using hder)
    · exact quarticADominant_constantLetters_impossible_of_beta
        (j := j) (t := t) beta gamma delta epsilon zeta eta theta A B C D
        E F G hApos hBn hCn hDn hEn hFn hGn hb0 hjdiv
        (by simpa [hl0] using hder)
  · exact quarticADominant_constantLetters_impossible_of_l
      (j := j) (t := t) l beta gamma delta epsilon zeta eta theta A B C D
      E F G hApos hBn hCn hDn hEn hFn hGn hl0 hjdiv hder


end QuarticSigmaCorners810
end Max11DegreeRoutes
end
