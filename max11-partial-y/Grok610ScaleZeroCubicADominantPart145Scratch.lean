import Grok610ScaleZeroCubicADominantPart144Scratch

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

section CubicAllLettersZero610

variable {k : Type*} [Field k] [CharZero k]

theorem cubicADominant_allLettersZero_impossible
    {j t : k}
    (l alpha beta delta epsilon zeta eta theta : k)
    (A B C D E : k[X])
    (hApos : 0 < A.natDegree)
    (hB : B = 0) (hC : C = 0) (hD : D = 0) (hE : E = 0)
    (hjdiv : j / t ≠ 0)
    (hder : derivative
        (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
          theta A B C D E) =
        Polynomial.C (j / t)) :
    False := by
  have hdeg :=
    natDegree_eq_one_of_derivative_eq_nonzero_C610
      (degreeZeroPrimitiveCubic610 l alpha beta delta epsilon zeta eta
        theta A B C D E) (j / t) hjdiv hder
  have hP := primitiveCubic_of_lettersBCDEzero l alpha beta delta epsilon
      zeta eta theta A B C D E hB hC hD hE
  rw [hP] at hder hdeg
  have hAne : A ≠ 0 := by
    intro h0
    have : A.natDegree = 0 := by simp [h0]
    omega
  have hle :
      ((5 / 27648 * l : k) • A ^ 7 +
          (35 / 62208 * beta : k) • A ^ 6 +
          (1 / 576 * delta : k) • A ^ 5 +
          (1 / 192 * zeta : k) • A ^ 4 +
          (1 / 72 * theta : k) • A ^ 3).natDegree ≤
        7 * A.natDegree := by
    compute_degree
  by_cases hl0 : l = 0
  · by_cases hb0 : beta = 0
    · by_cases hd0 : delta = 0
      · by_cases hz0 : zeta = 0
        · by_cases ht0 : theta = 0
          · simp only [hl0, hb0, hd0, hz0, ht0, mul_zero, zero_smul,
              add_zero] at hder
            have : derivative (0 : k[X]) = Polynomial.C (j / t) := hder
            rw [derivative_zero] at this
            exact hjdiv (C_eq_zero.mp this.symm)
          · have htheta : theta ≠ 0 := ht0
            have hc : (1 / 72 * theta : k) ≠ 0 :=
              mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) htheta
            have hcf :
                (((5 / 27648 * l : k) • A ^ 7 +
                      (35 / 62208 * beta : k) • A ^ 6 +
                      (1 / 576 * delta : k) • A ^ 5 +
                      (1 / 192 * zeta : k) • A ^ 4 +
                      (1 / 72 * theta : k) • A ^ 3).coeff (3 * A.natDegree)) ≠
                  0 := by
              simp only [hl0, hb0, hd0, hz0, mul_zero, zero_smul, zero_add]
              have hlead : ((1 / 72 * theta : k) • A ^ 3).coeff (3 * A.natDegree) =
                  (1 / 72 * theta : k) * A.leadingCoeff ^ 3 := by
                rw [coeff_smul]
                have hAk : (A ^ 3).natDegree = 3 * A.natDegree := natDegree_pow _ _
                rw [← hAk, coeff_natDegree, leadingCoeff_pow, smul_eq_mul]
              exact hlead ▸ mul_ne_zero hc
                (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hAne))
            have : 3 * A.natDegree ≤ 1 :=
              (le_natDegree_of_ne_zero hcf).trans_eq hdeg
            omega
        · have hzeta : zeta ≠ 0 := hz0
          have hc : (1 / 192 * zeta : k) ≠ 0 :=
            mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hzeta
          have hcf :
              (((5 / 27648 * l : k) • A ^ 7 +
                    (35 / 62208 * beta : k) • A ^ 6 +
                    (1 / 576 * delta : k) • A ^ 5 +
                    (1 / 192 * zeta : k) • A ^ 4 +
                    (1 / 72 * theta : k) • A ^ 3).coeff (4 * A.natDegree)) ≠
                0 := by
            simp only [hl0, hb0, hd0, mul_zero, zero_smul, zero_add]
            have hz3 : ((1 / 72 * theta : k) • A ^ 3).coeff (4 * A.natDegree) = 0 := by
              apply coeff_eq_zero_of_natDegree_lt
              compute_degree
              omega
            have hlead : ((1 / 192 * zeta : k) • A ^ 4).coeff (4 * A.natDegree) =
                (1 / 192 * zeta : k) * A.leadingCoeff ^ 4 := by
              rw [coeff_smul]
              have hAk : (A ^ 4).natDegree = 4 * A.natDegree := natDegree_pow _ _
              rw [← hAk, coeff_natDegree, leadingCoeff_pow, smul_eq_mul]
            simp only [coeff_add, hz3, add_zero, hlead]
            exact mul_ne_zero hc (pow_ne_zero 4 (leadingCoeff_ne_zero.mpr hAne))
          have : 4 * A.natDegree ≤ 1 :=
            (le_natDegree_of_ne_zero hcf).trans_eq hdeg
          omega
      · have hdelta : delta ≠ 0 := hd0
        have hc : (1 / 576 * delta : k) ≠ 0 :=
          mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hdelta
        have hcf :
            (((5 / 27648 * l : k) • A ^ 7 +
                  (35 / 62208 * beta : k) • A ^ 6 +
                  (1 / 576 * delta : k) • A ^ 5 +
                  (1 / 192 * zeta : k) • A ^ 4 +
                  (1 / 72 * theta : k) • A ^ 3).coeff (5 * A.natDegree)) ≠
              0 := by
          simp only [hl0, hb0, mul_zero, zero_smul, zero_add]
          have hz4 : ((1 / 192 * zeta : k) • A ^ 4).coeff (5 * A.natDegree) = 0 := by
            apply coeff_eq_zero_of_natDegree_lt
            compute_degree
            omega
          have hz3 : ((1 / 72 * theta : k) • A ^ 3).coeff (5 * A.natDegree) = 0 := by
            apply coeff_eq_zero_of_natDegree_lt
            compute_degree
            omega
          have hlead : ((1 / 576 * delta : k) • A ^ 5).coeff (5 * A.natDegree) =
              (1 / 576 * delta : k) * A.leadingCoeff ^ 5 := by
            rw [coeff_smul]
            have hAk : (A ^ 5).natDegree = 5 * A.natDegree := natDegree_pow _ _
            rw [← hAk, coeff_natDegree, leadingCoeff_pow, smul_eq_mul]
          simp only [coeff_add, hz4, hz3, add_zero, hlead]
          exact mul_ne_zero hc (pow_ne_zero 5 (leadingCoeff_ne_zero.mpr hAne))
        have : 5 * A.natDegree ≤ 1 :=
          (le_natDegree_of_ne_zero hcf).trans_eq hdeg
        omega
    · have hbeta : beta ≠ 0 := hb0
      have hc : (35 / 62208 * beta : k) ≠ 0 :=
        mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hbeta
      have hcf :
          (((5 / 27648 * l : k) • A ^ 7 +
                (35 / 62208 * beta : k) • A ^ 6 +
                (1 / 576 * delta : k) • A ^ 5 +
                (1 / 192 * zeta : k) • A ^ 4 +
                (1 / 72 * theta : k) • A ^ 3).coeff (6 * A.natDegree)) ≠
            0 := by
        simp only [hl0, mul_zero, zero_smul, zero_add]
        have hz5 : ((1 / 576 * delta : k) • A ^ 5).coeff (6 * A.natDegree) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          compute_degree
          omega
        have hz4 : ((1 / 192 * zeta : k) • A ^ 4).coeff (6 * A.natDegree) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          compute_degree
          omega
        have hz3 : ((1 / 72 * theta : k) • A ^ 3).coeff (6 * A.natDegree) = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          compute_degree
          omega
        have hlead : ((35 / 62208 * beta : k) • A ^ 6).coeff (6 * A.natDegree) =
            (35 / 62208 * beta : k) * A.leadingCoeff ^ 6 := by
          rw [coeff_smul]
          have hAk : (A ^ 6).natDegree = 6 * A.natDegree := natDegree_pow _ _
          rw [← hAk, coeff_natDegree, leadingCoeff_pow, smul_eq_mul]
        simp only [coeff_add, hz5, hz4, hz3, add_zero, hlead]
        exact mul_ne_zero hc (pow_ne_zero 6 (leadingCoeff_ne_zero.mpr hAne))
      have : 6 * A.natDegree ≤ 1 :=
        (le_natDegree_of_ne_zero hcf).trans_eq hdeg
      omega
  · have hl : l ≠ 0 := hl0
    have hc : (5 / 27648 * l : k) ≠ 0 :=
      mul_ne_zero (div_ne_zero (by norm_num) (by norm_num)) hl
    have hcf :
        (((5 / 27648 * l : k) • A ^ 7 +
              (35 / 62208 * beta : k) • A ^ 6 +
              (1 / 576 * delta : k) • A ^ 5 +
              (1 / 192 * zeta : k) • A ^ 4 +
              (1 / 72 * theta : k) • A ^ 3).coeff (7 * A.natDegree)) ≠
          0 := by
      have hz6 : ((35 / 62208 * beta : k) • A ^ 6).coeff (7 * A.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        compute_degree
        omega
      have hz5 : ((1 / 576 * delta : k) • A ^ 5).coeff (7 * A.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        compute_degree
        omega
      have hz4 : ((1 / 192 * zeta : k) • A ^ 4).coeff (7 * A.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        compute_degree
        omega
      have hz3 : ((1 / 72 * theta : k) • A ^ 3).coeff (7 * A.natDegree) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        compute_degree
        omega
      have hlead : ((5 / 27648 * l : k) • A ^ 7).coeff (7 * A.natDegree) =
          (5 / 27648 * l : k) * A.leadingCoeff ^ 7 := by
        rw [coeff_smul]
        have hAk : (A ^ 7).natDegree = 7 * A.natDegree := natDegree_pow _ _
        rw [← hAk, coeff_natDegree, leadingCoeff_pow, smul_eq_mul]
      simp only [coeff_add, hz6, hz5, hz4, hz3, add_zero, hlead]
      exact mul_ne_zero hc (pow_ne_zero 7 (leadingCoeff_ne_zero.mpr hAne))
    have : 7 * A.natDegree ≤ 1 :=
      (le_natDegree_of_ne_zero hcf).trans_eq hdeg
    omega

end CubicAllLettersZero610

end Max11DegreeRoutes
