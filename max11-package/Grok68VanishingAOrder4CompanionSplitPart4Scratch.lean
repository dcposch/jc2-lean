import Grok68VanishingAOrder4CompanionSplitPart3Scratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 4 of 26, so that no single
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

/-- Left factor of degree at least three, right factor of degree at least four. -/
theorem coeff_mul_sub_four_left_ge_three68 (f g : k[X]) (u v : ℕ)
    (hu : 3 ≤ u) (hv : 4 ≤ v) (hf : f.natDegree ≤ u) (hg : g.natDegree ≤ v) :
    (f * g).coeff (u + v - 4) =
      (if 4 ≤ u then f.coeff (u - 4) * g.coeff v else 0) +
        f.coeff (u - 3) * g.coeff (v - 1) +
        f.coeff (u - 2) * g.coeff (v - 2) +
        f.coeff (u - 1) * g.coeff (v - 3) +
        f.coeff u * g.coeff (v - 4) := by
  by_cases h4 : 4 ≤ u
  · rw [if_pos h4]
    exact coeff_mul_four_below_bounds68 f g u v h4 hv hf hg
  · have hu3 : u = 3 := by omega
    subst u
    rw [if_neg (by norm_num : ¬ 4 ≤ 3)]
    -- `u+v-4 = v-1`.  Expand the antidiagonal of length four.
    have hmem0 : 0 ∈ Finset.range (v - 1 + 1) :=
      Finset.mem_range.mpr (by omega)
    have hmem1 : 1 ∈ (Finset.range (v - 1 + 1)).erase 0 :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
    have hmem2 : 2 ∈ ((Finset.range (v - 1 + 1)).erase 0).erase 1 :=
      Finset.mem_erase.mpr ⟨by omega,
        Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩
    have hmem3 : 3 ∈ (((Finset.range (v - 1 + 1)).erase 0).erase 1).erase 2 :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
        Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩⟩
    have hzero : ∀ i ∈ ((((Finset.range (v - 1 + 1)).erase 0).erase 1).erase
          2).erase 3,
        f.coeff i * g.coeff (v - 1 - i) = 0 := by
      intro i hi
      have hi0 := Finset.mem_erase.mp hi
      have hi1 := Finset.mem_erase.mp hi0.2
      have hi2 := Finset.mem_erase.mp hi1.2
      have hi3 := Finset.mem_erase.mp hi2.2
      by_cases hgt : 3 < i
      · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt (by omega)), zero_mul]
      · omega
    have hsum : (f * g).coeff (v - 1) =
        ∑ i ∈ Finset.range (v - 1 + 1), f.coeff i * g.coeff (v - 1 - i) := by
      rw [coeff_mul]
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
    have h0 := Finset.add_sum_erase (Finset.range (v - 1 + 1))
      (fun i => f.coeff i * g.coeff (v - 1 - i)) hmem0
    have h1 := Finset.add_sum_erase ((Finset.range (v - 1 + 1)).erase 0)
      (fun i => f.coeff i * g.coeff (v - 1 - i)) hmem1
    have h2 := Finset.add_sum_erase
      (((Finset.range (v - 1 + 1)).erase 0).erase 1)
      (fun i => f.coeff i * g.coeff (v - 1 - i)) hmem2
    have h3 := Finset.add_sum_erase
      ((((Finset.range (v - 1 + 1)).erase 0).erase 1).erase 2)
      (fun i => f.coeff i * g.coeff (v - 1 - i)) hmem3
    have h4 : ∑ i ∈ ((((Finset.range (v - 1 + 1)).erase 0).erase 1).erase
          2).erase 3,
        f.coeff i * g.coeff (v - 1 - i) = 0 := Finset.sum_eq_zero hzero
    have hidx : 3 + v - 4 = v - 1 := by omega
    rw [hidx, hsum, ← h0, ← h1, ← h2, ← h3, h4, add_zero]
    rw [show v - 1 - 0 = v - 1 by omega, show v - 1 - 1 = v - 2 by omega,
      show v - 1 - 2 = v - 3 by omega, show v - 1 - 3 = v - 4 by omega]
    ring


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
