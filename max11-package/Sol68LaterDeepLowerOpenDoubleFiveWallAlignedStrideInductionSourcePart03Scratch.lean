import Sol68LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSourcePart02Scratch

/-! # Uniform aligned-stride induction on the degenerate double-five wall -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSource68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem laterDeepLowerOpenDoubleFiveWall_degenerate_aligned_offset_edges_zero68
    (n s : ℕ) (a b c₁ d₁ e : k)
    (hn : 0 < n) (hs : 3 * s < 5 * n) (ha : a ≠ 0) (hb : b ≠ 0)
    (hi3 : -a * b * d₁ - b ^ 2 * c₁ + 3 * c₁ * e = 0)
    (hrow :
      2 * a ^ 2 * b * d₁ * (5 * (n : k) - (s : k)) -
        6 * a * c₁ * e * (5 * (n : k) - (s : k)) -
        4 * (n : k) * a * b ^ 2 * c₁ = 0) : c₁ = 0 ∧ d₁ = 0 := by
  have hN : 7 * (n : k) - (s : k) ≠ 0 := by
    intro hz
    have hnat : 7 * n = s := by exact_mod_cast (sub_eq_zero.mp hz)
    omega
  have hcprod : a * b ^ 2 * c₁ * (7 * (n : k) - (s : k)) = 0 := by
    linear_combination (-1 / 2 : k) * hrow -
      a * (5 * (n : k) - (s : k)) * hi3
  have hc : c₁ = 0 := by
    rcases mul_eq_zero.mp hcprod with habc | hfac
    · rcases mul_eq_zero.mp habc with hab | hc
      · exact False.elim ((mul_ne_zero ha (pow_ne_zero 2 hb)) hab)
      · exact hc
    · exact False.elim (hN hfac)
  have hdprod : a * b * d₁ = 0 := by
    rw [hc] at hi3
    linear_combination -hi3
  have hd : d₁ = 0 :=
    (mul_eq_zero.mp hdprod).resolve_left (mul_ne_zero ha hb)
  exact ⟨hc, hd⟩

set_option maxHeartbeats 3000000 in
theorem secondaryLoadInvariantThreePolynomial68_degree_lt_aligned_offset_of_doubleFiveWall
    (gamma delta epsilon zeta : k) (A B c D e : k[X])
    (n g s : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n) (hs : s < 5 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - s)
    (hD : D.natDegree ≤ 5 * n - g)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantThreePolynomial68
      0 0 gamma delta epsilon zeta A B c D e).natDegree <
        10 * n - 3 * g - s := by
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, mul_zero,
    zero_smul, smul_zero, add_zero, sub_zero]
  compute_degree
  omega

end LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSource68
end Max11DegreeRoutes
