import Sol68LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSourcePart06Scratch

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

set_option maxHeartbeats 5000000 in
theorem secondaryLoadInvariantThreePolynomial68_coeff_terminal_aligned_offset_of_fiveWall
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (n g : ℕ) (hn : 0 < n)
    (hopen : 3 * n < 2 * g ∧ 2 * g < 5 * n)
    (hwall : 3 * g = 5 * n)
    (hA : A.natDegree ≤ 2 * n)
    (hB : B.natDegree ≤ 3 * n - g)
    (hc : c.natDegree ≤ 4 * n - g - (5 * n - 2 * g))
    (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 6 * n - 2 * g) :
    (secondaryLoadInvariantThreePolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff
        (10 * n - 3 * g - (5 * n - 2 * g)) =
      (-1 / 2 : k) * delta * A.coeff (2 * n) * B.coeff (3 * n - g) := by
  have htarget : 10 * n - 3 * g - (5 * n - 2 * g) = 5 * n - g := by
    omega
  have hAB := coeff_mul_at_bounds68 A B (2 * n) (3 * n - g) hA hB
  have hABi : 2 * n + (3 * n - g) = 5 * n - g := by omega
  rw [hABi] at hAB
  have hDcoeff : (((1 / 3 : k) • (A * B) + d).coeff (5 * n - g)) =
      (1 / 3 : k) * A.coeff (2 * n) * B.coeff (3 * n - g) := by
    rw [coeff_add, coeff_smul, hAB,
      coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))]
    ring
  have hzeta : (zeta • B).natDegree < 5 * n - g :=
    (natDegree_smul_le zeta B).trans_lt (hB.trans_lt (by omega))
  have heps : ((2 * epsilon : k) • c).natDegree < 5 * n - g :=
    (natDegree_smul_le _ c).trans_lt (hc.trans_lt (by omega))
  have hgammaE : ((4 * gamma : k) • e).natDegree < 5 * n - g :=
    (natDegree_smul_le _ e).trans_lt (he.trans_lt (by omega))
  have hB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree <
      5 * n - g := by
    compute_degree
    omega
  have hABcoeff : (A * B).coeff (5 * n - g) =
      A.coeff (2 * n) * B.coeff (3 * n - g) := hAB
  rw [htarget]
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, zero_smul,
    zero_add, add_zero, sub_zero, coeff_add, coeff_sub, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hzeta,
    coeff_eq_zero_of_natDegree_lt heps,
    coeff_eq_zero_of_natDegree_lt hgammaE,
    coeff_eq_zero_of_natDegree_lt hB2, hDcoeff, hABcoeff, smul_eq_mul]
  ring

end LaterDeepLowerOpenDoubleFiveWallAlignedStrideInductionSource68
end Max11DegreeRoutes
