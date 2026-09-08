import Sol68LaterDeepLowerParentFiveToSixOffsetOneEightyOrdinaryPairZeroScratch

/-! # Ordinary offset-240 pair-zero successor

The zero edge at offset `240` makes `d` vanish and drops `e` to its
constant edge.  I4 at coefficient `60` performs the second support drop;
I3 at coefficient `120` leaves the exact terminal load scalar.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryPairZero68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- With `d=0`, the next positive I4 coefficient is exactly the remaining
`e` edge. -/
theorem cubicFirstIntegralFourPolynomial68_coeff_sixty_offsetThreeHundred68
    (gamma epsilon : k) (A B c d e : k[X]) (hd : d = 0)
    (hB : B.natDegree ≤ 0) (he : e.natDegree ≤ 60) :
    (cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 60 =
      (8 / 3 : k) * B.coeff 0 * e.coeff 60 := by
  rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates,
    hd, coeff_add, coeff_add, coeff_add]
  have hB3 : (B ^ 3).natDegree < 60 := by compute_degree; omega
  have hBe := coeff_mul_at_bounds68 B e 0 60 hB he
  norm_num at hBe
  have hloadB : ((2 * epsilon : k) • B).natDegree < 60 := by
    compute_degree
    omega
  simp only [secondaryResidualInvariantFourPolynomial68, coeff_add,
    coeff_smul, smul_eq_mul, coeff_eq_zero_of_natDegree_lt hB3,
    hBe, coeff_zero, mul_zero, add_zero,
    coeff_eq_zero_of_natDegree_lt hloadB, zero_mul]
  ring

/-- Once `d=0` and `e` is constant, I3 at coefficient `120` is the exact
terminal epsilon/e load on the remaining `c` edge. -/
theorem cubicFirstIntegralThreePolynomial68_coeff_oneTwenty_terminal68
    (gamma epsilon : k) (A B c d e : k[X]) (hd : d = 0)
    (hB : B.natDegree ≤ 0) (hc : c.natDegree ≤ 120)
    (he : e.natDegree ≤ 0) :
    (cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 120 =
      c.coeff 120 *
        ((8 / 3 : k) * e.coeff 0 + 2 * epsilon -
          (8 / 9 : k) * B.coeff 0 ^ 2) := by
  rw [cubicFirstIntegralThreePolynomial68_fiveToSix_residualCoordinates,
    hd, coeff_sub, coeff_add, coeff_add, coeff_add]
  have hB2 : (B ^ 2).natDegree ≤ 0 := by compute_degree; omega
  have hB2c := coeff_mul_at_bounds68 (B ^ 2) c 0 120 hB2 hc
  norm_num [pow_two, mul_coeff_zero] at hB2c
  have hce := coeff_mul_at_bounds68 c e 120 0 hc he
  norm_num at hce
  have hloade : ((4 * gamma : k) • e).natDegree < 120 := by
    compute_degree
    omega
  have hB2coeff : (B ^ 2).coeff 120 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB2.trans_lt (by norm_num))
  have hBBcoeff : (B * B).coeff 120 = 0 := by
    simpa only [pow_two] using hB2coeff
  simp only [secondaryResidualInvariantThreePolynomial68, coeff_add,
    coeff_sub, coeff_smul, smul_eq_mul, coeff_zero, mul_zero, zero_mul,
    add_zero, zero_add, hB2coeff, pow_two, hB2c, hce,
    coeff_eq_zero_of_natDegree_lt hloade]
  rw [hBBcoeff]
  ring

set_option maxHeartbeats 12000000 in
/-- Exact source-facing terminal packet for the offset-`240` pair-zero
sibling.  The remaining alternative is either loss of the `c` top edge or
the displayed loaded epsilon/constant-`e` wall. -/
theorem fiveToSix_offsetTwoForty_ordinary_pairZero_source_packet68
    (gamma epsilon i4 i3 : k) (A B c d e qe : k[X])
    (hb : B.coeff 0 ≠ 0)
    (hB : B.natDegree ≤ 0) (hc : c.natDegree ≤ 120)
    (hd : d.natDegree ≤ 0) (he : e.natDegree ≤ 120)
    (heexpand : e = expand k 60 qe)
    (hpair : d.coeff 0 = 0 ∧ e.coeff 120 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    d = 0 ∧ e.natDegree ≤ 0 ∧
      (c.coeff 120 = 0 ∨
        9 * epsilon + 12 * e.coeff 0 - 4 * B.coeff 0 ^ 2 = 0) := by
  have hdpoly : d = 0 := by
    rw [eq_C_of_natDegree_le_zero hd, hpair.1]
    simp
  have he60 : e.natDegree ≤ 60 := by
    rw [heexpand]
    exact natDegree_expand_le_sub_twoForty_of_boundary_zero_oneEighty68
      qe 300 (by norm_num) (by norm_num)
      (by simpa only [heexpand] using he)
      (by simpa only [heexpand] using hpair.2)
  have hcoeff4 := congrArg (fun p : k[X] => p.coeff 60) hi4
  rw [cubicFirstIntegralFourPolynomial68_coeff_sixty_offsetThreeHundred68
      gamma epsilon A B c d e hdpoly hB he60] at hcoeff4
  norm_num [coeff_C] at hcoeff4
  have heEdge : e.coeff 60 = 0 := hcoeff4.resolve_left hb
  have he0 : e.natDegree ≤ 0 := by
    rw [heexpand]
    exact natDegree_expand_le_sub_twoForty_of_boundary_zero_oneEighty68
      qe 240 (by norm_num) (by norm_num)
      (by simpa only [heexpand] using he60)
      (by simpa only [heexpand] using heEdge)
  have hcoeff3 := congrArg (fun p : k[X] => p.coeff 120) hi3
  rw [cubicFirstIntegralThreePolynomial68_coeff_oneTwenty_terminal68
      gamma epsilon A B c d e hdpoly hB hc he0] at hcoeff3
  norm_num [coeff_C] at hcoeff3
  refine ⟨hdpoly, he0, ?_⟩
  rcases hcoeff3 with hcTop | hfactor
  · exact Or.inl hcTop
  · right
    linear_combination (9 / 2 : k) * hfactor

#print axioms cubicFirstIntegralFourPolynomial68_coeff_sixty_offsetThreeHundred68
#print axioms cubicFirstIntegralThreePolynomial68_coeff_oneTwenty_terminal68
#print axioms fiveToSix_offsetTwoForty_ordinary_pairZero_source_packet68

end LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryPairZero68

end Max11DegreeRoutes
