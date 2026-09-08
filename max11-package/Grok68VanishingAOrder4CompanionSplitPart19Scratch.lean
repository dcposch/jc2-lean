import Grok68VanishingAOrder4CompanionSplitPart18Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 19 of 26, so that no single
module retains all the reflective bridge proof terms at once.
Statements unchanged. -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000000

section FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

theorem fiveToSix_qZero_coeff_X_pow_mul_of_lt68
    (r : k) (p : k[X]) {n i : ℕ} (h : i < n) :
    (C r * X ^ n * p).coeff i = 0 := by
  have hXp : (X ^ n * p).coeff i = 0 := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [coeff_X_pow]
    split_ifs with heq
    · have : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      omega
    · rw [zero_mul]
  simp only [mul_assoc, coeff_C_mul, hXp, mul_zero]


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
