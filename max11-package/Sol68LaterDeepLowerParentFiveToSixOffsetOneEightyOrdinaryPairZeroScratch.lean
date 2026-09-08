import Sol68LaterDeepLowerParentFiveToSixOffsetOneTwentyOrdinaryPairZeroScratch

/-! # Ordinary offset-180 pair-zero successor

The zero sibling at offset `180` drops by `60`-expansion support to offset
`240`.  The new I4/I3 edge coefficients are `120` and `240` and remain
load-free because `zeta=0` on the ordinary wall.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryPairZero68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A `60`-expanded polynomial bounded at offset `180` drops to offset
`240` when its offset-`180` coefficient vanishes. -/
theorem natDegree_expand_le_sub_twoForty_of_boundary_zero_oneEighty68
    (q : k[X]) (base : ℕ) (hbase : 60 ∣ base) (hbase240 : 240 ≤ base)
    (hdeg : (expand k 60 q).natDegree ≤ base - 180)
    (h180 : (expand k 60 q).coeff (base - 180) = 0) :
    (expand k 60 q).natDegree ≤ base - 240 := by
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
    have hlt : base - 240 < (expand k 60 q).natDegree := by omega
    obtain ⟨u, hu⟩ := hbase
    obtain ⟨v, hv⟩ := hdiv
    have heq : (expand k 60 q).natDegree = base - 180 := by omega
    exact hlead (by simpa only [heq] using h180)

/-- Load-free I4 edge at ordinary offset `240`. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_oneTwenty_offsetTwoForty68
    (gamma epsilon : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 240) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 120) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 120) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 120 =
      (8 / 3 : k) *
        (B.coeff 0 * e.coeff 120 + c.coeff 120 * d.coeff 0) := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    coeff_add, coeff_add, coeff_add]
  have hB3 : (B ^ 3).natDegree < 120 := by compute_degree; omega
  have hBe := coeff_mul_at_bounds68 B e 0 120 hB he
  norm_num at hBe
  have hcd := coeff_mul_at_bounds68 c d 120 0 hc hd
  norm_num at hcd
  have hloadB : ((2 * epsilon : k) • B).natDegree < 120 := by
    compute_degree; omega
  have hloadd : ((4 * gamma : k) • d).natDegree < 120 := by
    compute_degree; omega
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3,
    hBe, hcd, coeff_eq_zero_of_natDegree_lt hloadB,
    coeff_eq_zero_of_natDegree_lt hloadd, zero_mul, add_zero]
  ring

/-- Load-free I3 edge at ordinary offset `240`. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_twoForty_offsetTwoForty68
    (gamma epsilon : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 240) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 120) (hd : d.natDegree ≤ 0)
    (he : e.natDegree ≤ 120) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 240 =
      (8 / 9 : k) *
        (-A.coeff 240 * B.coeff 0 * d.coeff 0 +
          3 * c.coeff 120 * e.coeff 120) := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    coeff_sub, coeff_add, coeff_add, coeff_add]
  have hABd := coeff_mul_mul_at_bounds68 A B d 240 0 0 hA hB hd
  norm_num at hABd
  have hB2c : (B ^ 2 * c).natDegree < 240 := by compute_degree; omega
  have hce := coeff_mul_at_bounds68 c e 120 120 hc he
  norm_num at hce
  have hd2 : (d ^ 2).natDegree < 240 := by compute_degree; omega
  have hloadc : ((2 * epsilon : k) • c).natDegree < 240 := by
    compute_degree; omega
  have hloade : ((4 * gamma : k) • e).natDegree < 240 := by
    compute_degree; omega
  have hloadB2 : ((2 / 3 * gamma : k) • B ^ 2).natDegree < 240 := by
    compute_degree; omega
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, hABd,
    coeff_eq_zero_of_natDegree_lt hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hd2,
    coeff_eq_zero_of_natDegree_lt hloadc,
    coeff_eq_zero_of_natDegree_lt hloade,
    coeff_eq_zero_of_natDegree_lt hloadB2, zero_mul, add_zero]
  ring

set_option maxHeartbeats 12000000 in
/-- Exact source-facing offset-`240` successor of the offset-`180` pair-zero
sibling.  It preserves both the next zero edge and the honest nonzero
discriminant alternative. -/
theorem fiveToSix_offsetOneEighty_ordinary_pairZero_source_packet68
    (gamma epsilon i4 i3 : k) (A B c d e qd qe : k[X])
    (ha : A.coeff 240 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hA : A.natDegree ≤ 240) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 120) (hd : d.natDegree ≤ 60)
    (he : e.natDegree ≤ 180)
    (hdexpand : d = expand k 60 qd) (heexpand : e = expand k 60 qe)
    (hpair : d.coeff 60 = 0 ∧ e.coeff 180 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    d.natDegree ≤ 0 ∧ e.natDegree ≤ 120 ∧
      ((d.coeff 0 = 0 ∧ e.coeff 120 = 0) ∨
        (B.coeff 0 ≠ 0 ∧ c.coeff 120 ≠ 0 ∧
          d.coeff 0 ≠ 0 ∧ e.coeff 120 ≠ 0 ∧
          A.coeff 240 * B.coeff 0 ^ 2 + 3 * c.coeff 120 ^ 2 = 0)) := by
  have hd240 : d.natDegree ≤ 0 := by
    rw [hdexpand]
    exact natDegree_expand_le_sub_twoForty_of_boundary_zero_oneEighty68
      qd 240 (by norm_num) (by norm_num)
      (by simpa only [hdexpand] using hd)
      (by simpa only [hdexpand] using hpair.1)
  have he240 : e.natDegree ≤ 120 := by
    rw [heexpand]
    exact natDegree_expand_le_sub_twoForty_of_boundary_zero_oneEighty68
      qe 360 (by norm_num) (by norm_num)
      (by simpa only [heexpand] using he)
      (by simpa only [heexpand] using hpair.2)
  have hcoeff4 := congrArg (fun p : k[X] => p.coeff 120) hi4
  rw [cubicFirstIntegralFourPolynomial68_coeff_oneTwenty_offsetTwoForty68
    gamma epsilon A B c d e hA hB hc hd240 he240] at hcoeff4
  norm_num [coeff_C] at hcoeff4
  have hfour : B.coeff 0 * e.coeff 120 +
      c.coeff 120 * d.coeff 0 = 0 := by
    exact hcoeff4
  have hcoeff3 := congrArg (fun p : k[X] => p.coeff 240) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_twoForty_offsetTwoForty68
    gamma epsilon A B c d e hA hB hc hd240 he240] at hcoeff3
  norm_num [coeff_C] at hcoeff3
  have hthree : -A.coeff 240 * B.coeff 0 * d.coeff 0 +
      3 * c.coeff 120 * e.coeff 120 = 0 := by
    linear_combination hcoeff3
  have hface : SecondaryResidualBetweenFace68
      (A.coeff 240) (B.coeff 0) (c.coeff 120)
      (d.coeff 0) (e.coeff 120) := ⟨hfour, hthree⟩
  refine ⟨hd240, he240, ?_⟩
  by_cases hedge : d.coeff 0 = 0 ∧ e.coeff 120 = 0
  · exact Or.inl hedge
  · right
    have hattained : d.coeff 0 ≠ 0 ∨ e.coeff 120 ≠ 0 := by tauto
    exact secondaryResidualBetweenFace68_classify_of_support
      (A.coeff 240) (B.coeff 0) (c.coeff 120)
      (d.coeff 0) (e.coeff 120) ha (Or.inl hb) hattained hface

#print axioms natDegree_expand_le_sub_twoForty_of_boundary_zero_oneEighty68
#print axioms cubicFirstIntegralFourPolynomial68_coeff_oneTwenty_offsetTwoForty68
#print axioms cubicFirstIntegralThreePolynomial68_coeff_twoForty_offsetTwoForty68
#print axioms fiveToSix_offsetOneEighty_ordinary_pairZero_source_packet68

end LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryPairZero68

end Max11DegreeRoutes
