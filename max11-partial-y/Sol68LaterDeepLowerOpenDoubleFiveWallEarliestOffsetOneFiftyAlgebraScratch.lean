import Sol68LaterDeepLowerOpenDoubleFiveWallEarliestLoadSourceScratch

/-! # The first delta-loaded face after the earliest double-five load -/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerOpenDoubleFiveWallEarliestOffsetOneFiftyAlgebra68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem natDegree_expand_le_sixty_of_le_oneTwenty_coeff_oneTwenty_zero68
    (q : k[X]) (hdeg : (expand k 60 q).natDegree ≤ 120)
    (hedge : (expand k 60 q).coeff 120 = 0) :
    (expand k 60 q).natDegree ≤ 60 := by
  simpa using natDegree_expand_le_sub_sixty_of_aligned_boundary_zero68
    q 120 (by norm_num) (by norm_num) hdeg hedge

theorem natDegree_expand_le_zero_of_le_sixty_coeff_sixty_zero68
    (q : k[X]) (hdeg : (expand k 60 q).natDegree ≤ 60)
    (hedge : (expand k 60 q).coeff 60 = 0) :
    (expand k 60 q).natDegree ≤ 0 := by
  simpa using natDegree_expand_le_sub_sixty_of_aligned_boundary_zero68
    q 60 (by norm_num) (by norm_num) hdeg hedge

set_option maxHeartbeats 5000000 in
theorem secondaryResidualInvariantThreePolynomial68_coeff_earliest_offsetOneFifty
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 180) (hB : B.natDegree ≤ 120)
    (hc : c.natDegree ≤ 60) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 240) :
    (secondaryResidualInvariantThreePolynomial68 A B c d e).coeff 300 =
      (8 / 9 : k) *
        (-(A.coeff 180 * B.coeff 120 * d.coeff 0) -
          B.coeff 120 ^ 2 * c.coeff 60 +
          3 * c.coeff 60 * e.coeff 240) := by
  have hABd := coeff_mul_mul_at_bounds68 A B d 180 120 0 hA hB hd
  have hBBc := coeff_mul_mul_at_bounds68 B B c 120 120 60 hB hB hc
  have hB2c : (B ^ 2 * c).coeff 300 =
      B.coeff 120 ^ 2 * c.coeff 60 := by
    simpa only [pow_two] using hBBc
  have hce := coeff_mul_at_bounds68 c e 60 240 hc he
  have hd2 : (d ^ 2).natDegree < 300 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd, hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2]
  ring

set_option maxHeartbeats 5000000 in
theorem secondaryLoadInvariantThreePolynomial68_coeff_earliest_offsetOneFifty
    (gamma delta epsilon zeta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 180) (hB : B.natDegree ≤ 120)
    (hc : c.natDegree ≤ 60) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 240) :
    (secondaryLoadInvariantThreePolynomial68 0 0 gamma delta epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 300 =
      (-1 / 2 : k) * delta * A.coeff 180 * B.coeff 120 := by
  have hAB := coeff_mul_at_bounds68 A B 180 120 hA hB
  have hDcoeff : (((1 / 3 : k) • (A * B) + d).coeff 300) =
      (1 / 3 : k) * A.coeff 180 * B.coeff 120 := by
    rw [coeff_add, coeff_smul, hAB,
      coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))]
    ring
  have hzeta : (zeta • B).natDegree < 300 :=
    (natDegree_smul_le zeta B).trans_lt (hB.trans_lt (by omega))
  have heps : ((2 * epsilon : k) • c).natDegree < 300 :=
    (natDegree_smul_le _ c).trans_lt (hc.trans_lt (by omega))
  have hgammaE : ((4 * gamma : k) • e).natDegree < 300 :=
    (natDegree_smul_le _ e).trans_lt (he.trans_lt (by omega))
  have hB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree < 300 := by
    compute_degree
    omega
  have hABcoeff : (A * B).coeff 300 = A.coeff 180 * B.coeff 120 := hAB
  simp only [secondaryLoadInvariantThreePolynomial68, zero_mul, zero_smul,
    zero_add, add_zero, sub_zero, coeff_add, coeff_sub, coeff_smul,
    coeff_eq_zero_of_natDegree_lt hzeta,
    coeff_eq_zero_of_natDegree_lt heps,
    coeff_eq_zero_of_natDegree_lt hgammaE,
    coeff_eq_zero_of_natDegree_lt hB2, hDcoeff, hABcoeff, smul_eq_mul]
  ring

theorem earliest_offsetOneFifty_deltaLoaded_scalar68
    (a b c₁ d₁ e delta : k)
    (hresidual : (8 / 9 : k) *
      (-a * b * d₁ - b ^ 2 * c₁ + 3 * c₁ * e) +
        (-1 / 2 : k) * delta * a * b = 0) :
    (8 / 9 : k) *
      (-a * b * d₁ - b ^ 2 * c₁ + 3 * c₁ * e) =
        (1 / 2 : k) * delta * a * b := by
  linear_combination hresidual

#print axioms natDegree_expand_le_sixty_of_le_oneTwenty_coeff_oneTwenty_zero68
#print axioms natDegree_expand_le_zero_of_le_sixty_coeff_sixty_zero68
#print axioms secondaryResidualInvariantThreePolynomial68_coeff_earliest_offsetOneFifty
#print axioms secondaryLoadInvariantThreePolynomial68_coeff_earliest_offsetOneFifty
#print axioms earliest_offsetOneFifty_deltaLoaded_scalar68

end LaterDeepLowerOpenDoubleFiveWallEarliestOffsetOneFiftyAlgebra68

end Max11DegreeRoutes
