import LowScale68SecondaryLaterDeepLowerOpenMiddleHighCoincidentSevenEndgamePart01Scratch

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

set_option maxHeartbeats 4000000 in
theorem coincidentSevenRowZeroLoad68_coeff
    (gamma epsilon zeta : k) (A B c d e : k[X])
    (n g h : ℕ) (hn : 0 < n) (hg : 0 < g)
    (hwallH : 2 * h = 7 * n) (hwallG : 3 * g = 7 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g)
    (hd : d.natDegree ≤ 5 * n - h)
    (he : e.natDegree ≤ 6 * n - h) :
    (coincidentSevenRowZeroLoad68 gamma epsilon zeta A B c d e).coeff
        (6 * n - 1) =
      (2 / 9 : k) * (n : k) * zeta * A.coeff (2 * n) ^ 3 := by
  have hlow :=
    fiveRadiusTerminalRowZeroLoad68_degree_lt_sixRadius_of_coincidentSeven
      gamma epsilon A B c d e n g h hn hg hwallH hwallG hA hB hc hd he
  have hA3deg : (A ^ 3).natDegree ≤ 6 * n := by
    compute_degree
    omega
  have hA3 : (A ^ 3).coeff (6 * n) = A.coeff (2 * n) ^ 3 := by
    have ht := coeff_pow_at_bound68 A (2 * n) 3 hA
    have hi : 3 * (2 * n) = 6 * n := by omega
    simpa only [hi] using ht
  have hAclt : (A * c).natDegree < 6 * n := by
    compute_degree
    omega
  have helt : e.natDegree < 6 * n := he.trans_lt (by omega)
  have htop :
      (((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e).coeff
        (6 * n)) = (1 / 27 : k) * A.coeff (2 * n) ^ 3 := by
    simp only [coeff_add, coeff_smul, smul_eq_mul, hA3,
      coeff_eq_zero_of_natDegree_lt hAclt,
      coeff_eq_zero_of_natDegree_lt helt, mul_zero, add_zero]
  have hder := coeff_derivative_at_bound68
    ((1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e)
    (6 * n) (by omega)
  rw [htop] at hder
  simp only [coincidentSevenRowZeroLoad68, coeff_add,
    coeff_eq_zero_of_natDegree_lt hlow, zero_add, coeff_smul, smul_eq_mul,
    hder]
  push_cast
  ring

end LaterDeepLowerOpenMiddleHighCoincidentSevenEndgame68
end Max11DegreeRoutes
