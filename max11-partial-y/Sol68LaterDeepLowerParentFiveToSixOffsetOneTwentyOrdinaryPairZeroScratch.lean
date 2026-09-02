import Sol68LaterDeepLowerParentFiveToSixOffsetOneTwentyOneThreeRowZeroScratch

/-! # Ordinary offset-120 pair-zero successor

At the numeric ordinary wall `(n,g)=(120,360)`, a zero offset-`120`
edge pair drops by expansion support to offset `180`.  The next unused I4
and I3 coefficients are respectively `180` and `300`; both are load-free
when `zeta=0`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryPairZero68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A `60`-expanded polynomial bounded at offset `120` drops to offset
`180` when its offset-`120` coefficient vanishes. -/
theorem natDegree_expand_le_sub_oneEighty_of_boundary_zero_oneTwenty68
    (q : k[X]) (base : ℕ) (hbase : 60 ∣ base) (hbase180 : 180 ≤ base)
    (hdeg : (expand k 60 q).natDegree ≤ base - 120)
    (h120 : (expand k 60 q).coeff (base - 120) = 0) :
    (expand k 60 q).natDegree ≤ base - 180 := by
  by_cases hq : expand k 60 q = 0
  · rw [hq, natDegree_zero]
    omega
  · have hlead :
        (expand k 60 q).coeff (expand k 60 q).natDegree ≠ 0 := by
      rw [coeff_natDegree, leadingCoeff]
      exact Polynomial.leadingCoeff_ne_zero.mpr hq
    have hdiv : 60 ∣ (expand k 60 q).natDegree :=
      coeff_expand_ne_zero_dvd68 60 (by norm_num) q
        (expand k 60 q).natDegree hlead
    by_contra hnot
    have hlt : base - 180 < (expand k 60 q).natDegree := by omega
    obtain ⟨u, hu⟩ := hbase
    obtain ⟨v, hv⟩ := hdiv
    have heq : (expand k 60 q).natDegree = base - 120 := by omega
    exact hlead (by simpa only [heq] using h120)

/-- The next unused ordinary I4 coefficient, at degree `180`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_oneEighty_ordinaryWall68
    (gamma epsilon : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 240) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 120) (hd : d.natDegree ≤ 60)
    (he : e.natDegree ≤ 180) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 180 =
      (8 / 3 : k) *
        (B.coeff 0 * e.coeff 180 + c.coeff 120 * d.coeff 60) := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add]
  have hB3 : (B ^ 3).natDegree < 180 := by compute_degree; omega
  have hBe := coeff_mul_at_bounds68 B e 0 180 hB he
  norm_num at hBe
  have hcd := coeff_mul_at_bounds68 c d 120 60 hc hd
  norm_num at hcd
  have hloadB : ((2 * epsilon : k) • B).natDegree < 180 := by
    compute_degree
    omega
  have hloadd : ((4 * gamma : k) • d).natDegree < 180 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3,
    hBe, hcd, coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd, zero_mul, add_zero]
  ring

/-- The companion ordinary I3 coefficient, at degree `300`. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_threeHundred_ordinaryWall68
    (gamma epsilon : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 240) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 120) (hd : d.natDegree ≤ 60)
    (he : e.natDegree ≤ 180) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 300 =
      (8 / 9 : k) *
        (-A.coeff 240 * B.coeff 0 * d.coeff 60 +
          3 * c.coeff 120 * e.coeff 180) := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add]
  have hABd := coeff_mul_mul_at_bounds68 A B d 240 0 60 hA hB hd
  norm_num at hABd
  have hB2c : (B ^ 2 * c).natDegree < 300 := by compute_degree; omega
  have hce := coeff_mul_at_bounds68 c e 120 180 hc he
  norm_num at hce
  have hd2 : (d ^ 2).natDegree < 300 := by compute_degree; omega
  have hloadB : (0 • B).natDegree < 300 := by simp
  have hloadc : ((2 * epsilon : k) • c).natDegree < 300 := by
    compute_degree
    omega
  have hloade : ((4 * gamma : k) • e).natDegree < 300 := by
    compute_degree
    omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree < 300 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2,
    coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2, zero_mul, add_zero]
  ring

set_option maxHeartbeats 15000000 in
/-- Exact source-facing successor of the ordinary offset-`120` pair-zero
branch.  It reaches the offset-`180` face and retains both its zero and
nonzero-discriminant alternatives. -/
theorem fiveToSix_offsetOneTwenty_ordinary_pairZero_source_packet68
    (gamma epsilon i4 i3 : k) (A B c d e qd qe : k[X])
    (ha : A.coeff 240 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hA : A.natDegree ≤ 240) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 120) (hd : d.natDegree ≤ 120)
    (he : e.natDegree ≤ 240)
    (hdexpand : d = expand k 60 qd) (heexpand : e = expand k 60 qe)
    (hpair : d.coeff 120 = 0 ∧ e.coeff 240 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    d.natDegree ≤ 60 ∧ e.natDegree ≤ 180 ∧
      ((d.coeff 60 = 0 ∧ e.coeff 180 = 0) ∨
        (B.coeff 0 ≠ 0 ∧ c.coeff 120 ≠ 0 ∧
          d.coeff 60 ≠ 0 ∧ e.coeff 180 ≠ 0 ∧
          A.coeff 240 * B.coeff 0 ^ 2 + 3 * c.coeff 120 ^ 2 = 0)) := by
  have hd180 : d.natDegree ≤ 60 := by
    rw [hdexpand]
    exact natDegree_expand_le_sub_oneEighty_of_boundary_zero_oneTwenty68
      qd 240 (by norm_num) (by norm_num)
      (by simpa only [hdexpand] using hd)
      (by simpa only [hdexpand] using hpair.1)
  have he180 : e.natDegree ≤ 180 := by
    rw [heexpand]
    exact natDegree_expand_le_sub_oneEighty_of_boundary_zero_oneTwenty68
      qe 360 (by norm_num) (by norm_num)
      (by simpa only [heexpand] using he)
      (by simpa only [heexpand] using hpair.2)
  have hcoeff4 := congrArg (fun p : k[X] => p.coeff 180) hi4
  rw [cubicFirstIntegralFourPolynomial68_coeff_oneEighty_ordinaryWall68
    gamma epsilon A B c d e hA hB hc hd180 he180] at hcoeff4
  norm_num [coeff_C] at hcoeff4
  have hfour : B.coeff 0 * e.coeff 180 +
      c.coeff 120 * d.coeff 60 = 0 := by
    exact hcoeff4
  have hcoeff3 := congrArg (fun p : k[X] => p.coeff 300) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_threeHundred_ordinaryWall68
    gamma epsilon A B c d e hA hB hc hd180 he180] at hcoeff3
  norm_num [coeff_C] at hcoeff3
  have hthree : -A.coeff 240 * B.coeff 0 * d.coeff 60 +
      3 * c.coeff 120 * e.coeff 180 = 0 := by
    linear_combination hcoeff3
  have hface : SecondaryResidualBetweenFace68
      (A.coeff 240) (B.coeff 0) (c.coeff 120)
      (d.coeff 60) (e.coeff 180) := ⟨hfour, hthree⟩
  refine ⟨hd180, he180, ?_⟩
  by_cases hedge : d.coeff 60 = 0 ∧ e.coeff 180 = 0
  · exact Or.inl hedge
  · right
    have hattained : d.coeff 60 ≠ 0 ∨ e.coeff 180 ≠ 0 := by tauto
    exact secondaryResidualBetweenFace68_classify_of_support
      (A.coeff 240) (B.coeff 0) (c.coeff 120)
      (d.coeff 60) (e.coeff 180) ha (Or.inl hb) hattained hface

#print axioms natDegree_expand_le_sub_oneEighty_of_boundary_zero_oneTwenty68
#print axioms cubicFirstIntegralFourPolynomial68_coeff_oneEighty_ordinaryWall68
#print axioms cubicFirstIntegralThreePolynomial68_coeff_threeHundred_ordinaryWall68
#print axioms fiveToSix_offsetOneTwenty_ordinary_pairZero_source_packet68

end LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryPairZero68

end Max11DegreeRoutes
