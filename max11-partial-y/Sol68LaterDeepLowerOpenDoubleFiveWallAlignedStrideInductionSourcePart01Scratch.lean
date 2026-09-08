import Sol68LaterDeepLowerOpenDoubleFiveWallAlignedOneEightySourceScratch

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

set_option maxHeartbeats 4000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_aligned_offset_of_fiveWall
    (A B c d e : k[X]) (n g s : ℕ)
    (hn : 0 < n) (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n) (hs : s ≤ 5 * n - 2 * g)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - s)
    (hd : d.natDegree ≤ 5 * n - 2 * g - s)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff
        (10 * n - 3 * g - s) =
      (8 / 9 : k) *
        (-(A.coeff (2 * n) * B.coeff (3 * n - g) *
            d.coeff (5 * n - 2 * g - s)) -
          B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g - s) +
          3 * c.coeff (4 * n - g - s) *
            e.coeff (6 * n - 2 * g)) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d (2 * n)
    (3 * n - g) (5 * n - 2 * g - s) hA hB hd
  have hABdi : 2 * n + (3 * n - g) + (5 * n - 2 * g - s) =
      10 * n - 3 * g - s := by omega
  rw [hABdi] at hABd
  have hBBc := coeff_mul_mul_at_bounds68 B B c (3 * n - g)
    (3 * n - g) (4 * n - g - s) hB hB hc
  have hBBci : (3 * n - g) + (3 * n - g) + (4 * n - g - s) =
      10 * n - 3 * g - s := by omega
  rw [hBBci] at hBBc
  have hB2c : (B ^ 2 * c).coeff (10 * n - 3 * g - s) =
      B.coeff (3 * n - g) ^ 2 * c.coeff (4 * n - g - s) := by
    simpa only [pow_two] using hBBc
  have hce := coeff_mul_at_bounds68 c e (4 * n - g - s)
    (6 * n - 2 * g) hc he
  have hcei : (4 * n - g - s) + (6 * n - 2 * g) =
      10 * n - 3 * g - s := by omega
  rw [hcei] at hce
  have hd2 : (d ^ 2).natDegree < 10 * n - 3 * g - s := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

end LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSource68
end Max11DegreeRoutes
