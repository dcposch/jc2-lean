import Grok68VanishingAOrder4CompanionSplitBaseScratch

/-! # SPEED: theorems of `Grok68VanishingAOrder4CompanionScratch`, part 0 of 26, so that no single
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

/-- Four coefficients below a product of two separate bounds. -/
theorem coeff_mul_four_below_bounds68 (f g : k[X]) (u v : ℕ)
    (hu : 4 ≤ u) (hv : 4 ≤ v) (hf : f.natDegree ≤ u) (hg : g.natDegree ≤ v) :
    (f * g).coeff (u + v - 4) =
      f.coeff (u - 4) * g.coeff v + f.coeff (u - 3) * g.coeff (v - 1) +
        f.coeff (u - 2) * g.coeff (v - 2) + f.coeff (u - 1) * g.coeff (v - 3) +
        f.coeff u * g.coeff (v - 4) := by
  have hmem0 : u - 4 ∈ Finset.range (u + v - 4 + 1) :=
    Finset.mem_range.mpr (by omega)
  have hmem1 : u - 3 ∈ (Finset.range (u + v - 4 + 1)).erase (u - 4) :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  have hmem2 : u - 2 ∈
      ((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase (u - 3) :=
    Finset.mem_erase.mpr ⟨by omega,
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩
  have hmem3 : u - 1 ∈
      (((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase (u - 3)).erase
        (u - 2) :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩⟩
  have hmem4 : u ∈
      ((((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase (u - 3)).erase
        (u - 2)).erase (u - 1) :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega,
        Finset.mem_range.mpr (by omega)⟩⟩⟩⟩
  have hzero : ∀ i ∈ (((((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase
        (u - 3)).erase (u - 2)).erase (u - 1)).erase u,
      f.coeff i * g.coeff (u + v - 4 - i) = 0 := by
    intro i hi
    have hi0 := Finset.mem_erase.mp hi
    have hi1 := Finset.mem_erase.mp hi0.2
    have hi2 := Finset.mem_erase.mp hi1.2
    have hi3 := Finset.mem_erase.mp hi2.2
    have hi4 := Finset.mem_erase.mp hi3.2
    by_cases hgt : u < i
    · rw [coeff_eq_zero_of_natDegree_lt (hf.trans_lt hgt), zero_mul]
    · have : i < u - 4 := by omega
      rw [coeff_eq_zero_of_natDegree_lt (hg.trans_lt (by omega)), mul_zero]
  have hsum : (f * g).coeff (u + v - 4) =
      ∑ i ∈ Finset.range (u + v - 4 + 1), f.coeff i * g.coeff (u + v - 4 - i) := by
    rw [coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ _
  have h0 := Finset.add_sum_erase (Finset.range (u + v - 4 + 1))
    (fun i => f.coeff i * g.coeff (u + v - 4 - i)) hmem0
  have h1 := Finset.add_sum_erase ((Finset.range (u + v - 4 + 1)).erase (u - 4))
    (fun i => f.coeff i * g.coeff (u + v - 4 - i)) hmem1
  have h2 := Finset.add_sum_erase
    (((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase (u - 3))
    (fun i => f.coeff i * g.coeff (u + v - 4 - i)) hmem2
  have h3 := Finset.add_sum_erase
    ((((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase (u - 3)).erase (u - 2))
    (fun i => f.coeff i * g.coeff (u + v - 4 - i)) hmem3
  have h4 := Finset.add_sum_erase
    (((((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase (u - 3)).erase
      (u - 2)).erase (u - 1))
    (fun i => f.coeff i * g.coeff (u + v - 4 - i)) hmem4
  have h5 : ∑ i ∈ (((((Finset.range (u + v - 4 + 1)).erase (u - 4)).erase
        (u - 3)).erase (u - 2)).erase (u - 1)).erase u,
      f.coeff i * g.coeff (u + v - 4 - i) = 0 :=
    Finset.sum_eq_zero hzero
  rw [hsum, ← h0, ← h1, ← h2, ← h3, ← h4, h5, add_zero]
  rw [show u + v - 4 - (u - 4) = v by omega,
    show u + v - 4 - (u - 3) = v - 1 by omega,
    show u + v - 4 - (u - 2) = v - 2 by omega,
    show u + v - 4 - (u - 1) = v - 3 by omega,
    show u + v - 4 - u = v - 4 by omega]
  ring


end FiveToSixCuspLoadedLowerRowZetaFirstUniformJetEndpointB3EqualityEpsilonSupportQZeroVanishingAOrder4Companion68

end Max11DegreeRoutes

end
