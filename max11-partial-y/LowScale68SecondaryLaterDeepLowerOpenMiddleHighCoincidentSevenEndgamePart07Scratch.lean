import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentSevenEndgamePart06Scratch

/-! # Closure for the coincident seven wall `2h=3g=7n` -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The quartic incidence defect on the coincident wall -/

/-! ## Row zero at `6n-1` -/

/-! ## Row one after the row-zero/row-two cancellation -/

set_option maxHeartbeats 11000000 in
theorem fiveRadiusBalancedRowOneCore68_coeff_of_coincidentSeven
    (A B c d e : k[X]) (n g h : ℕ)
    (hn : 0 < n) (hg : 0 < g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (fiveRadiusBalancedRowOneCore68 A B c d e).coeff (5 * n - 1) =
      (-4 / 27 : k) *
        (A.coeff (2 * n) *
            ((3 : k) * d.coeff (5 * n - h) ^ 2 -
              (2 : k) * B.coeff (3 * n - g) ^ 2 *
                c.coeff (4 * n - g)) * ((5 * n : ℕ) : k) +
          (6 : k) * ((4 * n - g : ℕ) : k) *
            c.coeff (4 * n - g) ^ 3 -
          (18 : k) * ((6 * n - h : ℕ) : k) *
            e.coeff (6 * n - h) ^ 2) := by
  have hd2deg : (d ^ 2).natDegree ≤ 2 * (5 * n - h) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hd
  have hd2 : (d ^ 2).coeff (2 * (5 * n - h)) =
      d.coeff (5 * n - h) ^ 2 :=
    coeff_pow_at_bound68 d (5 * n - h) 2 hd
  have hAd2 := coeff_mul_at_bounds68 A (d ^ 2)
    (2 * n) (2 * (5 * n - h)) hA hd2deg
  have hiAd2 : 2 * n + 2 * (5 * n - h) = 5 * n := by omega
  rw [hiAd2, hd2] at hAd2
  have hAd2' := coeff_derivative_at_bound68 (A * d ^ 2) (5 * n) (by omega)
  rw [hAd2] at hAd2'
  have hB2deg : (B ^ 2).natDegree ≤ 2 * (3 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hB
  have hB2 : (B ^ 2).coeff (2 * (3 * n - g)) =
      B.coeff (3 * n - g) ^ 2 :=
    coeff_pow_at_bound68 B (3 * n - g) 2 hB
  have hAB2c := coeff_mul_mul_at_bounds68 A (B ^ 2) c
    (2 * n) (2 * (3 * n - g)) (4 * n - g) hA hB2deg hc
  have hiAB2c : 2 * n + 2 * (3 * n - g) + (4 * n - g) = 5 * n := by
    omega
  rw [hiAB2c, hB2] at hAB2c
  have hAB2c' := coeff_derivative_at_bound68 (A * B ^ 2 * c)
    (5 * n) (by omega)
  rw [hAB2c] at hAB2c'
  have hc2deg : (c ^ 2).natDegree ≤ 2 * (4 * n - g) := by
    compute_degree
    exact Nat.mul_le_mul_left 2 hc
  have hc2 : (c ^ 2).coeff (2 * (4 * n - g)) =
      c.coeff (4 * n - g) ^ 2 :=
    coeff_pow_at_bound68 c (4 * n - g) 2 hc
  have hc3 := coeff_mul_derivative_at_bounds68 (c ^ 2) c
    (2 * (4 * n - g)) (4 * n - g) (by omega) hc2deg hc
  have hic3 : 2 * (4 * n - g) + (4 * n - g) - 1 = 5 * n - 1 := by
    omega
  rw [hic3, hc2] at hc3
  have hee := coeff_mul_derivative_at_bounds68 e e
    (6 * n - h) (6 * n - h) (by omega) he he
  have hiee : (6 * n - h) + (6 * n - h) - 1 = 5 * n - 1 := by omega
  rw [hiee] at hee
  simp only [fiveRadiusBalancedRowOneCore68, coeff_smul, coeff_add,
    smul_eq_mul, hAd2', hAB2c', hc3, hee]
  ring

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
