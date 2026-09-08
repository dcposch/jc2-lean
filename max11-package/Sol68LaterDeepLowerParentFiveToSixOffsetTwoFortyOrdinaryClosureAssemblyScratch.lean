import Sol68LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryPairZeroClosureScratch

/-! # Offset-240 ordinary closure assembly

This is the common source-facing wrapper for the ordinary offset-`240`
selector.  The selector itself is run on the canonical `60`-expansion;
only its boundary coefficients are transported back to the contracted
chart.  The exact contracted first integrals and three source rows then
close respectively the pair-zero and all-nonzero successors.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryAssembly68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The compact quartic first integral commutes with polynomial expansion. -/
theorem expand_cubicFirstIntegralFourPolynomial68
    (m : ℕ) (l beta gamma delta epsilon zeta : k)
    (A B c D e : k[X]) :
    expand k m (cubicFirstIntegralFourPolynomial68
        l beta gamma delta epsilon zeta A B c D e) =
      cubicFirstIntegralFourPolynomial68 l beta gamma delta epsilon zeta
        (expand k m A) (expand k m B) (expand k m c)
        (expand k m D) (expand k m e) := by
  simp [cubicFirstIntegralFourPolynomial68]

/-- The compact cubic first integral commutes with polynomial expansion. -/
theorem expand_cubicFirstIntegralThreePolynomial68
    (m : ℕ) (l beta gamma delta epsilon zeta : k)
    (A B c D e : k[X]) :
    expand k m (cubicFirstIntegralThreePolynomial68
        l beta gamma delta epsilon zeta A B c D e) =
      cubicFirstIntegralThreePolynomial68 l beta gamma delta epsilon zeta
        (expand k m A) (expand k m B) (expand k m c)
        (expand k m D) (expand k m e) := by
  simp [cubicFirstIntegralThreePolynomial68]

set_option maxHeartbeats 30000000 in
/-- The ordinary offset-`240` packet is empty.  The hypotheses are the
contracted source chart: offset `180` is the vanishing pair `d₁=e₃=0`,
the two first integrals are constant, and all three literal residual/load
rows vanish. -/
theorem fiveToSix_offsetTwoForty_ordinary_source_closure68
    (alpha gamma epsilon eta i4 i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 3)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hpair : d.coeff 1 = 0 ∧ e.coeff 3 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow0 : secondaryResidualRowZeroPolynomial68 A B c d e +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow1 : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow2 : secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) : False := by
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let ce := expand k 60 c
  let de := expand k 60 d
  let ee := expand k 60 e
  have hAe : Ae.natDegree ≤ 240 := by
    simp only [Ae, natDegree_expand]
    omega
  have hBe : Be.natDegree ≤ 0 := by
    simp only [Be, natDegree_expand]
    omega
  have hce : ce.natDegree ≤ 120 := by
    simp only [ce, natDegree_expand]
    omega
  have hde : de.natDegree ≤ 60 := by
    simp only [de, natDegree_expand]
    omega
  have hee : ee.natDegree ≤ 180 := by
    simp only [ee, natDegree_expand]
    omega
  have haE : Ae.coeff 240 ≠ 0 := by
    simpa [Ae, coeff_expand] using ha
  have hbE : Be.coeff 0 ≠ 0 := by
    simpa [Be, coeff_expand] using hb
  have hpairE : de.coeff 60 = 0 ∧ ee.coeff 180 = 0 := by
    simpa [de, ee, coeff_expand] using hpair
  have hi4e : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + de) ee = C i4 := by
    have h := congrArg (expand k 60) hi4
    simpa only [Ae, Be, ce, de, ee, expand_C,
      expand_cubicFirstIntegralFourPolynomial68, map_add, map_mul,
      map_smul] using h
  have hi3e : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + de) ee = C i3 := by
    have h := congrArg (expand k 60) hi3
    simpa only [Ae, Be, ce, de, ee, expand_C,
      expand_cubicFirstIntegralThreePolynomial68, map_add, map_mul,
      map_smul] using h
  have hrow0c (j : ℕ) :
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff j = 0 := by
    rw [hrow0]
    simp
  have hrow1c (j : ℕ) :
      (secondaryResidualRowOnePolynomial68 A B c d e +
        cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff j = 0 := by
    rw [hrow1]
    simp
  have hrow2c (j : ℕ) :
      (secondaryResidualRowTwoPolynomial68 A B c d e +
        cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff j = 0 := by
    rw [hrow2]
    simp
  have hselector :=
    fiveToSix_offsetOneEighty_ordinary_pairZero_source_packet68
      gamma epsilon i4 i3 Ae Be ce de ee d e haE hbE hAe hBe hce hde hee
      rfl rfl hpairE hi4e hi3e
  have hd0 : d.natDegree ≤ 0 := by
    have h := hselector.1
    simp only [de, natDegree_expand] at h
    omega
  have he2 : e.natDegree ≤ 2 := by
    have h := hselector.2.1
    simp only [ee, natDegree_expand] at h
    omega
  rcases hselector.2.2 with hzeroE | hnzE
  · have hzero : d.coeff 0 = 0 ∧ e.coeff 2 = 0 := by
      simpa [de, ee, coeff_expand] using hzeroE
    have hterminalE :=
      fiveToSix_offsetTwoForty_ordinary_pairZero_source_packet68
        gamma epsilon i4 i3 Ae Be ce de ee e hbE hBe hce
        hselector.1 hselector.2.1 rfl hzeroE hi4e hi3e
    have hdpoly : d = 0 := by
      rw [eq_C_of_natDegree_le_zero hd0, hzero.1]
      simp
    have he0 : e.natDegree ≤ 0 := by
      have h := hterminalE.2.1
      simp only [ee, natDegree_expand] at h
      omega
    have hterminal : c.coeff 2 = 0 ∨
        9 * epsilon + 12 * e.coeff 0 - 4 * B.coeff 0 ^ 2 = 0 := by
      simpa [ce, ee, Be, coeff_expand] using hterminalE.2.2
    exact fiveToSix_offsetTwoForty_ordinary_pairZero_source_closure68
      alpha gamma epsilon eta i3 A B c d e hA hB hc hdpoly he0 ha hb
      hterminal hi3 (hrow0c 7) (hrow1c 5) (hrow0c 3)
      (hrow1c 3) (hrow2c 3)
  · have hnz : B.coeff 0 ≠ 0 ∧ c.coeff 2 ≠ 0 ∧
        d.coeff 0 ≠ 0 ∧ e.coeff 2 ≠ 0 ∧
        A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0 := by
      simpa [Ae, Be, ce, de, ee, coeff_expand] using hnzE
    have hcoeff4 := congrArg (fun p : k[X] => p.coeff 120) hi4e
    rw [cubicFirstIntegralFourPolynomial68_coeff_oneTwenty_offsetTwoForty68
      gamma epsilon Ae Be ce de ee hAe hBe hce hselector.1
        hselector.2.1] at hcoeff4
    norm_num [coeff_C] at hcoeff4
    have hfaceE : Be.coeff 0 * ee.coeff 120 +
        ce.coeff 120 * de.coeff 0 = 0 := by
      exact hcoeff4
    have hface : B.coeff 0 * e.coeff 2 +
        c.coeff 2 * d.coeff 0 = 0 := by
      simpa [Be, ce, de, ee, coeff_expand] using hfaceE
    have hcoeff1 := congrArg (fun p : k[X] => p.coeff 1) hi4
    rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
      at hcoeff1
    have hB1 : B.coeff 1 = 0 :=
      coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
    have hd1 : d.coeff 1 = 0 :=
      coeff_eq_zero_of_natDegree_lt (hd0.trans_lt (by norm_num))
    have hBcubeDeg : (B ^ 3).natDegree ≤ 0 := by
      compute_degree
      omega
    have hBcube1 : (B ^ 3).coeff 1 = 0 :=
      coeff_eq_zero_of_natDegree_lt (hBcubeDeg.trans_lt (by norm_num))
    norm_num [secondaryResidualInvariantFourPolynomial68, coeff_add,
      coeff_smul, smul_eq_mul, mul_coeff_one, coeff_C, hB1, hd1,
      hBcube1] at hcoeff1
    have hfirst : B.coeff 0 * e.coeff 1 +
        c.coeff 1 * d.coeff 0 = 0 := by
      have hs : (8 / 3 : k) *
          (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0) = 0 := by
        linear_combination hcoeff1
      exact (mul_eq_zero.mp hs).resolve_left (by norm_num)
    have hrigid := fiveToSix_offsetTwoForty_nonzero_rowZero_source_packet68
      alpha gamma epsilon eta i4 A B c d e hA hB hc hd0 he2 ha hb
      hnz.2.1 hnz.2.2.1 hnz.2.2.2.1 hface hnz.2.2.2.2 hi4
      (hrow0c 7)
    have hjet :=
      (fiveToSix_offsetTwoForty_nonzero_rowZero_six_source_packet68
        alpha gamma epsilon eta i4 A B c d e hA hB hc hd0 he2 ha hb
        hnz.2.1 hnz.2.2.1 hnz.2.2.2.1 hface hnz.2.2.2.2 hrigid
        hi4 (hrow0c 6)).2
    have hsecond :=
      (fiveToSix_offsetTwoForty_nonzero_rowZero_five_source_packet68
        alpha gamma epsilon eta i4 A B c d e hA hB hc hd0 he2 ha hb
        hnz.2.1 hnz.2.2.1 hnz.2.2.2.1 hface hnz.2.2.2.2 hrigid hjet
        hi4 (hrow0c 5)).2.2
    have hcoeff0 := congrArg (fun p : k[X] => p.coeff 0) hi4
    rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
      at hcoeff0
    have hBcube0 : (B ^ 3).coeff 0 = B.coeff 0 ^ 3 := by
      simp only [pow_succ, mul_coeff_zero]
      norm_num [coeff_one]
    norm_num [secondaryResidualInvariantFourPolynomial68, coeff_add,
      coeff_smul, smul_eq_mul, mul_coeff_zero, coeff_C, hBcube0] at hcoeff0
    have hconstant : (-8 / 27 : k) * B.coeff 0 ^ 3 +
        (8 / 3 : k) *
          (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
        2 * epsilon * B.coeff 0 + 4 * gamma * d.coeff 0 = i4 := by
      linear_combination hcoeff0
    have hwall : 4 * A.coeff 4 *
          (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
        3 * A.coeff 4 * epsilon * B.coeff 0 +
        6 * A.coeff 4 * gamma * d.coeff 0 -
          4 * B.coeff 0 * c.coeff 2 ^ 2 = 0 := by
      linear_combination (1 / 18 : k) * hrigid +
        (3 / 2 : k) * A.coeff 4 * hconstant -
        (4 / 3 : k) * B.coeff 0 * hnz.2.2.2.2
    have hscalar :=
      fiveToSix_offsetTwoForty_nonzero_terminal_i3_source_packet68
        gamma epsilon i3 A B c d e hA hB hc hd0 he2 ha hb hnz.2.1
        hnz.2.2.1 hnz.2.2.2.1 hface hnz.2.2.2.2 hfirst hwall
        hsecond hi3
    have hthird :=
      (fiveToSix_offsetTwoForty_nonzero_rowZero_four_source_packet68
        alpha gamma epsilon eta A B c d e hA hB hc hd0 he2 ha hb
        hnz.2.1 hnz.2.2.1 hnz.2.2.2.1 hface hnz.2.2.2.2 hfirst hjet
        hwall hsecond hscalar (hrow0c 4)).2
    have hfourth :=
      (fiveToSix_offsetTwoForty_nonzero_rowZero_three_source_packet68
        alpha gamma epsilon eta A B c d e hA hB hc hd0 he2 ha hb
        hnz.2.1 hnz.2.2.1 hnz.2.2.2.1 hface hnz.2.2.2.2 hfirst hjet
        hwall hsecond hscalar hthird (hrow0c 3)).2.2
    exact fiveToSix_offsetTwoForty_nonzero_rowZero_one_source_closure68
      alpha gamma epsilon eta A B c d e hA hB hc hd0 he2 ha hb hnz.2.1
      hnz.2.2.1 hface hnz.2.2.2.2 hfirst hjet hwall hsecond hscalar
      hthird hfourth (hrow0c 1)

#print axioms expand_cubicFirstIntegralFourPolynomial68
#print axioms expand_cubicFirstIntegralThreePolynomial68
#print axioms fiveToSix_offsetTwoForty_ordinary_source_closure68

end LaterDeepLowerParentFiveToSixOffsetTwoFortyOrdinaryAssembly68

end Max11DegreeRoutes
