import Grok68VanishingAOrder4CompanionSplitPart0Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 1 of 26, so that no single
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

/-- Degree-two coefficient of a product of two cubics. -/
theorem coeff_mul_at_two_of_degree_le_three68 (f g : k[X])
    (hf : f.natDegree ≤ 3) (hg : g.natDegree ≤ 3) :
    (f * g).coeff 2 =
      f.coeff 0 * g.coeff 2 + f.coeff 1 * g.coeff 1 + f.coeff 2 * g.coeff 0 := by
  have hmem0 : 0 ∈ Finset.range (2 + 1) := by simp
  have hmem1 : 1 ∈ (Finset.range (2 + 1)).erase 0 := by simp
  have hmem2 : 2 ∈ ((Finset.range (2 + 1)).erase 0).erase 1 := by simp
  have hzero : ∀ i ∈ (((Finset.range (2 + 1)).erase 0).erase 1).erase 2,
      f.coeff i * g.coeff (2 - i) = 0 := by
    intro i hi
    have hi0 := Finset.mem_erase.mp hi
    have hi1 := Finset.mem_erase.mp hi0.2
    have hi2 := Finset.mem_erase.mp hi1.2
    have : i ∈ Finset.range 3 := hi2.2
    have : i < 3 := Finset.mem_range.mp this
    omega
  have hsum : (f * g).coeff 2 =
      ∑ i ∈ Finset.range (2 + 1), f.coeff i * g.coeff (2 - i) := by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have h0 := Finset.add_sum_erase (Finset.range (2 + 1))
    (fun i => f.coeff i * g.coeff (2 - i)) hmem0
  have h1 := Finset.add_sum_erase ((Finset.range (2 + 1)).erase 0)
    (fun i => f.coeff i * g.coeff (2 - i)) hmem1
  have h2 := Finset.add_sum_erase (((Finset.range (2 + 1)).erase 0).erase 1)
    (fun i => f.coeff i * g.coeff (2 - i)) hmem2
  have h3 : ∑ i ∈ (((Finset.range (2 + 1)).erase 0).erase 1).erase 2,
      f.coeff i * g.coeff (2 - i) = 0 := Finset.sum_eq_zero hzero
  rw [hsum, ← h0, ← h1, ← h2, h3, add_zero]
  ring


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
