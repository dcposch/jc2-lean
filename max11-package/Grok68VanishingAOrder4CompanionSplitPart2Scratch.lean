import Grok68VanishingAOrder4CompanionSplitPart1Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 2 of 26, so that no single
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

/-- Square coefficient four below `2v`, allowing the short chart `v=3`. -/
theorem coeff_sq_sub_four68 (q : k[X]) (v : ℕ)
    (hv : 3 ≤ v) (hq : q.natDegree ≤ v) :
    (q ^ 2).coeff (2 * v - 4) =
      (2 : k) * q.coeff v * (if 4 ≤ v then q.coeff (v - 4) else 0) +
        (2 : k) * q.coeff (v - 1) * q.coeff (v - 3) + q.coeff (v - 2) ^ 2 := by
  by_cases h4 : 4 ≤ v
  · have h := coeff_mul_four_below_bounds68 q q v v h4 h4 hq hq
    rw [← two_mul] at h
    simp only [pow_two] at h ⊢
    rw [if_pos h4]
    linear_combination h
  · have hv3 : v = 3 := by omega
    subst v
    have h := coeff_mul_at_two_of_degree_le_three68 q q
      (by simpa using hq) (by simpa using hq)
    simp only [pow_two] at h ⊢
    rw [if_neg (by norm_num : ¬ 4 ≤ 3)]
    linear_combination h


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
