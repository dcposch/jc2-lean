import Sol68LaterDeepLowerParentFiveToSixTerminalRHSAdapterScratch

/-! # Terminal-safe positive-coefficient ordinary selector

All row-zero coefficients consumed by the offset-`120` ordinary descent are
strictly positive: `9`; then `7,6,5,4`; and at the offset-`240` terminal
`7,6,5,4,3,1`.  This file gives the weakest parallel assembly interface,
replacing row-zero polynomial equality by vanishing of positive
coefficients.  Rows one and two remain exact polynomial equalities.  No
coefficient algebra is repeated.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixPositiveCoefficientSelector68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Terminal-safe offset-`240` assembly.  This is the existing selector
assembly with only its row-zero coefficient accessor weakened. -/
theorem fiveToSix_offsetTwoForty_ordinary_positive_source_closure68
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
    (hrow0pos : ∀ j, 0 < j →
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff j = 0)
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
  have hAe : Ae.natDegree ≤ 240 := by simp only [Ae, natDegree_expand]; omega
  have hBe : Be.natDegree ≤ 0 := by simp only [Be, natDegree_expand]; omega
  have hce : ce.natDegree ≤ 120 := by simp only [ce, natDegree_expand]; omega
  have hde : de.natDegree ≤ 60 := by simp only [de, natDegree_expand]; omega
  have hee : ee.natDegree ≤ 180 := by simp only [ee, natDegree_expand]; omega
  have haE : Ae.coeff 240 ≠ 0 := by simpa [Ae, coeff_expand] using ha
  have hbE : Be.coeff 0 ≠ 0 := by simpa [Be, coeff_expand] using hb
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
      hterminal hi3 (hrow0pos 7 (by norm_num)) (hrow1c 5)
      (hrow0pos 3 (by norm_num)) (hrow1c 3) (hrow2c 3)
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
        ce.coeff 120 * de.coeff 0 = 0 := hcoeff4
    have hface : B.coeff 0 * e.coeff 2 + c.coeff 2 * d.coeff 0 = 0 := by
      simpa [Be, ce, de, ee, coeff_expand] using hfaceE
    have hcoeff1 := congrArg (fun p : k[X] => p.coeff 1) hi4
    rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
      at hcoeff1
    have hB1 : B.coeff 1 = 0 :=
      coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
    have hd1 : d.coeff 1 = 0 :=
      coeff_eq_zero_of_natDegree_lt (hd0.trans_lt (by norm_num))
    have hBcubeDeg : (B ^ 3).natDegree ≤ 0 := by compute_degree; omega
    have hBcube1 : (B ^ 3).coeff 1 = 0 :=
      coeff_eq_zero_of_natDegree_lt (hBcubeDeg.trans_lt (by norm_num))
    norm_num [secondaryResidualInvariantFourPolynomial68, coeff_add,
      coeff_smul, smul_eq_mul, mul_coeff_one, coeff_C, hB1, hd1,
      hBcube1] at hcoeff1
    have hfirst : B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 = 0 := by
      have hs : (8 / 3 : k) *
          (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0) = 0 := by
        linear_combination hcoeff1
      exact (mul_eq_zero.mp hs).resolve_left (by norm_num)
    have hrigid := fiveToSix_offsetTwoForty_nonzero_rowZero_source_packet68
      alpha gamma epsilon eta i4 A B c d e hA hB hc hd0 he2 ha hb
      hnz.2.1 hnz.2.2.1 hnz.2.2.2.1 hface hnz.2.2.2.2 hi4
      (hrow0pos 7 (by norm_num))
    have hjet :=
      (fiveToSix_offsetTwoForty_nonzero_rowZero_six_source_packet68
        alpha gamma epsilon eta i4 A B c d e hA hB hc hd0 he2 ha hb
        hnz.2.1 hnz.2.2.1 hnz.2.2.2.1 hface hnz.2.2.2.2 hrigid
        hi4 (hrow0pos 6 (by norm_num))).2
    have hsecond :=
      (fiveToSix_offsetTwoForty_nonzero_rowZero_five_source_packet68
        alpha gamma epsilon eta i4 A B c d e hA hB hc hd0 he2 ha hb
        hnz.2.1 hnz.2.2.1 hnz.2.2.2.1 hface hnz.2.2.2.2 hrigid hjet
        hi4 (hrow0pos 5 (by norm_num))).2.2
    have hcoeff0 := congrArg (fun p : k[X] => p.coeff 0) hi4
    rw [cubicFirstIntegralFourPolynomial68_fiveToSix_residualCoordinates]
      at hcoeff0
    have hBcube0 : (B ^ 3).coeff 0 = B.coeff 0 ^ 3 := by
      simp only [pow_succ, mul_coeff_zero]
      norm_num [coeff_one]
    norm_num [secondaryResidualInvariantFourPolynomial68, coeff_add,
      coeff_smul, smul_eq_mul, mul_coeff_zero, coeff_C, hBcube0] at hcoeff0
    have hconstant : (-8 / 27 : k) * B.coeff 0 ^ 3 +
        (8 / 3 : k) * (B.coeff 0 * e.coeff 0 + c.coeff 0 * d.coeff 0) +
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
        hwall hsecond hscalar (hrow0pos 4 (by norm_num))).2
    have hfourth :=
      (fiveToSix_offsetTwoForty_nonzero_rowZero_three_source_packet68
        alpha gamma epsilon eta A B c d e hA hB hc hd0 he2 ha hb
        hnz.2.1 hnz.2.2.1 hnz.2.2.2.1 hface hnz.2.2.2.2 hfirst hjet
        hwall hsecond hscalar hthird (hrow0pos 3 (by norm_num))).2.2
    exact fiveToSix_offsetTwoForty_nonzero_rowZero_one_source_closure68
      alpha gamma epsilon eta A B c d e hA hB hc hd0 he2 ha hb hnz.2.1
      hnz.2.2.1 hface hnz.2.2.2.2 hfirst hjet hwall hsecond hscalar
      hthird hfourth (hrow0pos 1 (by norm_num))

/-- Complete terminal-safe ordinary offset-`120` selector. -/
theorem fiveToSix_offsetOneTwenty_ordinary_positive_source_false68
    (alpha gamma epsilon zeta eta i4 i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 2)
    (he : e.natDegree ≤ 4)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow0pos : ∀ j, 0 < j →
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff j = 0)
    (hrow1 : secondaryResidualRowOnePolynomial68 A B c d e +
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0)
    (hrow2 : secondaryResidualRowTwoPolynomial68 A B c d e +
      cubicLoadRowTwoPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c ((1 / 3 : k) • (A * B) + d) e = 0) : False := by
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let ce := expand k 60 c
  let de := expand k 60 d
  let ee := expand k 60 e
  have hAe : Ae.natDegree ≤ 240 := by simp only [Ae, natDegree_expand]; omega
  have hBe : Be.natDegree ≤ 0 := by simp only [Be, natDegree_expand]; omega
  have hce : ce.natDegree ≤ 120 := by simp only [ce, natDegree_expand]; omega
  have hde : de.natDegree ≤ 120 := by simp only [de, natDegree_expand]; omega
  have hee : ee.natDegree ≤ 240 := by simp only [ee, natDegree_expand]; omega
  have haE : Ae.coeff 240 ≠ 0 := by simpa [Ae, coeff_expand] using ha
  have hbE : Be.coeff 0 ≠ 0 := by simpa [Be, coeff_expand] using hb
  have hi4e : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + de) ee = C i4 := by
    have h := congrArg (expand k 60) hi4
    simpa only [Ae, Be, ce, de, ee, expand_C,
      expand_cubicFirstIntegralFourPolynomial68, map_add, map_mul,
      map_smul] using h
  have hi3e : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
      Ae Be ce ((1 / 3 : k) • (Ae * Be) + de) ee = C i3 := by
    have h := congrArg (expand k 60) hi3
    simpa only [Ae, Be, ce, de, ee, expand_C,
      expand_cubicFirstIntegralThreePolynomial68, map_add, map_mul,
      map_smul] using h
  let P : k[X] := secondaryResidualRowZeroPolynomial68 A B c d e +
    cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e
  have hPdeg : P.natDegree ≤ 0 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (by
      intro j hj
      exact hrow0pos j (by omega))
  have hrowExpand := fiveToSix_residualLoadRowZero_expand68
    60 alpha gamma epsilon zeta eta A B c d e
  change secondaryResidualRowZeroPolynomial68 Ae Be ce de ee +
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        Ae Be ce ((1 / 3 : k) • (Ae * Be) + de) ee =
      expand k 60 P * (60 * (X ^ 59 : k[X])) at hrowExpand
  have hPexpand : (expand k 60 P).natDegree ≤ 0 := by
    simp only [natDegree_expand]
    omega
  have hrow719 :
      (secondaryResidualRowZeroPolynomial68 Ae Be ce de ee +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          Ae Be ce ((1 / 3 : k) • (Ae * Be) + de) ee).coeff 719 = 0 := by
    rw [hrowExpand]
    apply coeff_eq_zero_of_natDegree_lt
    compute_degree
    omega
  have hselect := fiveToSix_offsetOneTwenty_wall_source_zeta_zero68
    alpha gamma epsilon zeta eta i4 i3 Ae Be ce de ee haE hbE hAe hBe
    hce hde hee hi4e hi3e hrow719
  have hzeta : zeta = 0 := hselect.1
  have hi4z := hi4
  have hi3z := hi3
  have hrow1z := hrow1
  have hrow2z := hrow2
  rw [hzeta] at hi4z hi3z hrow1z hrow2z
  have hrow0posz : ∀ j, 0 < j →
      (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff j = 0 := by
    intro j hj
    have h := hrow0pos j hj
    simpa only [hzeta] using h
  rcases hselect.2 with hzeroE | hnzE
  · have hzero : d.coeff 2 = 0 ∧ e.coeff 4 = 0 := by
      simpa [de, ee, coeff_expand] using hzeroE
    have hnext := fiveToSix_offsetOneTwenty_ordinary_pairZero_source_packet68
      gamma epsilon i4 i3 Ae Be ce de ee d e haE hbE hAe hBe hce hde hee
      rfl rfl hzeroE (by simpa only [hzeta] using hi4e)
        (by simpa only [hzeta] using hi3e)
    have hd1 : d.natDegree ≤ 1 := by
      have h := hnext.1
      simp only [de, natDegree_expand] at h
      omega
    have he3 : e.natDegree ≤ 3 := by
      have h := hnext.2.1
      simp only [ee, natDegree_expand] at h
      omega
    rcases hnext.2.2 with hzeroNextE | hnzNextE
    · have hzeroNext : d.coeff 1 = 0 ∧ e.coeff 3 = 0 := by
        simpa [de, ee, coeff_expand] using hzeroNextE
      exact fiveToSix_offsetTwoForty_ordinary_positive_source_closure68
        alpha gamma epsilon eta i4 i3 A B c d e hA hB hc hd1 he3 ha hb
        hzeroNext hi4z hi3z hrow0posz hrow1z hrow2z
    · have hnzNext : B.coeff 0 ≠ 0 ∧ c.coeff 2 ≠ 0 ∧
          d.coeff 1 ≠ 0 ∧ e.coeff 3 ≠ 0 ∧
          A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0 := by
        simpa [Ae, Be, ce, de, ee, coeff_expand] using hnzNextE
      have hcoeff4 := congrArg (fun p : k[X] => p.coeff 180)
        (by simpa only [hzeta] using hi4e)
      rw [cubicFirstIntegralFourPolynomial68_coeff_oneEighty_ordinaryWall68
        gamma epsilon Ae Be ce de ee hAe hBe hce hnext.1 hnext.2.1]
          at hcoeff4
      norm_num [coeff_C] at hcoeff4
      have hface : B.coeff 0 * e.coeff 3 +
          c.coeff 2 * d.coeff 1 = 0 := by
        simpa [Be, ce, de, ee, coeff_expand] using hcoeff4
      have hrow7 := hrow0posz 7 (by norm_num)
      have hi4rigid :=
        fiveToSix_offsetOneEighty_nonzero_rowZero_source_packet68
          alpha gamma epsilon eta i4 A B c d e hA hB hc hd1 he3 ha hb
          hnzNext.2.1 hnzNext.2.2.1 hnzNext.2.2.2.1 hface
          hnzNext.2.2.2.2 hi4z hrow7
      let Cc : k[X] := (1 / 3 : k) • A ^ 2 + c
      let D0 : k[X] := (1 / 3 : k) • (A * B) + d
      let E0 : k[X] :=
        (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      have hcoords := integratedPolynomial68_cubicCoordinates
        (0 : k) alpha 0 gamma 0 epsilon 0 eta A B c D0 e
      have hhom1 : cubicHomogeneousRowOnePolynomial68 A B c D0 e =
          secondaryResidualRowOnePolynomial68 A B c d e := by
        simpa only [D0] using
          cubicHomogeneousRowOnePolynomial68_residualCoordinates A B c d e
      have hrowOneSource : lowerRowOnePolynomial68
          (integratedTPolynomial68 0 alpha 0 gamma epsilon A B Cc D0 E0)
          (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B Cc D0 E0)
          (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
            A B Cc D0 E0) Cc D0 E0 = 0 := by
        rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
          cubicRowOnePolynomial68_split, hhom1]
        exact hrow1z
      have hrowOnePacket :=
        fiveToSix_offsetOneEighty_nonzero_rowOne_source_packet68
          alpha gamma epsilon eta i4 i3 A B c d e hA hB hc hd1 he3 ha hb
          hnzNext.2.1 hnzNext.2.2.1 hnzNext.2.2.2.1 hface
          hnzNext.2.2.2.2 hi4rigid hi3z
          (by simpa only [Cc, D0, E0] using hrowOneSource)
      have hedge : 9 * e.coeff 3 ^ 2 - 4 * c.coeff 2 ^ 3 = 0 :=
        hrowOnePacket.2.1
      obtain ⟨hjetDisc, hjetEdge, hjetLoad⟩ :=
        fiveToSix_offsetOneEighty_ordinaryNonzeroNext_source_packet68
          alpha gamma epsilon eta i4 i3 A B c d e hA hB hc hd1 he3 ha hb
          hnzNext.2.1 hnzNext.2.2.1 hnzNext.2.2.2.1 hface
          hnzNext.2.2.2.2 hi4rigid hi4z hi3z
          (hrow0posz 6 (by norm_num))
      have hhom0 : cubicHomogeneousRowZeroPolynomial68 A B c D0 e =
          secondaryResidualRowZeroPolynomial68 A B c d e := by
        simpa only [D0] using
          cubicHomogeneousRowZeroPolynomial68_residualCoordinates A B c d e
      have hrowZeroResidual : lowerRowZeroPolynomial68
          (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B Cc D0 E0)
          (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
            A B Cc D0 E0) D0 E0 =
          secondaryResidualRowZeroPolynomial68 A B c d e +
            cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
              A B c D0 e := by
        rw [hcoords.u_eq, hcoords.v_eq, cubicRowZeroPolynomial68_split,
          hhom0]
      have hrow5 : (lowerRowZeroPolynomial68
          (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B Cc D0 E0)
          (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
            A B Cc D0 E0) D0 E0).coeff 5 = 0 := by
        rw [hrowZeroResidual]
        exact hrow0posz 5 (by norm_num)
      have hrow4 : (lowerRowZeroPolynomial68
          (integratedUPolynomial68 0 alpha 0 gamma 0 0 A B Cc D0 E0)
          (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
            A B Cc D0 E0) D0 E0).coeff 4 = 0 := by
        rw [hrowZeroResidual]
        exact hrow0posz 4 (by norm_num)
      exact fiveToSix_offsetOneEighty_ordinaryNextJoin_source_false68
        alpha gamma epsilon eta i4 i3 A B c d e hA hB hc hd1 he3 ha hb
        hnzNext.2.1 hnzNext.2.2.1 hnzNext.2.2.2.1 hface
        hnzNext.2.2.2.2 hi4rigid hedge hjetDisc hjetEdge hjetLoad
        hi4z hi3z (by simpa only [Cc, D0, E0] using hrow5)
        (by simpa only [Cc, D0, E0] using hrow4)
  · have hnz : B.coeff 0 ≠ 0 ∧ c.coeff 2 ≠ 0 ∧
        d.coeff 2 ≠ 0 ∧ e.coeff 4 ≠ 0 ∧
        A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0 := by
      simpa [Ae, Be, ce, de, ee, coeff_expand] using hnzE
    exact fiveToSix_offsetOneTwenty_ordinary_nonzero_source_false68
      alpha gamma epsilon eta i4 A B c d e hA hB hc hd he ha hb
      hnz.2.1 hnz.2.2.1 hnz.2.2.2.1 hnz.2.2.2.2 hi4z
      (hrow0posz 9 (by norm_num))

set_option maxHeartbeats 30000000 in
/-- At the global `(n,g)=(120,360)` wall the terminal-safe selector removes
the zero offset-`60` branch whenever the ordinary top `B₀` is present.
What remains is exactly the `B=0` sibling or the aligned nonzero offset-`60`
packet from OffsetNinety. -/
theorem maximalExpandedIntegratedPolynomialLowerSystem_offsetOneTwenty_ordinary_positive_reduction68
    (l alpha beta gamma delta epsilon zeta eta terminal : k)
    (A B C0 D E : k[X]) (hterminal : terminal ≠ 0)
    (hsys : IntegratedPolynomialLowerSystem68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E)
    (hlater :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      3 * n ≤ 2 * g)
    (hwall :
      let n := weightedRadius68 A B C0 D E
      let Ae := expand k 60 A
      let Be := expand k 60 B
      let Ce := expand k 60 C0
      let ce := cubicCDefectPolynomial68 Ae Ce
      let De := expand k 60 D
      let Ee := expand k 60 E
      let ee := cubicEDefectPolynomial68 Ae Ce Ee
      let g := cubicDefectGap68 n Be ce De ee
      n = 120 ∧ g = 360) :
    let n := weightedRadius68 A B C0 D E
    let Ae := expand k 60 A
    let Be := expand k 60 B
    let Ce := expand k 60 C0
    let ce := cubicCDefectPolynomial68 Ae Ce
    let De := expand k 60 D
    let Ee := expand k 60 E
    let ee := cubicEDefectPolynomial68 Ae Ce Ee
    let g := cubicDefectGap68 n Be ce De ee
    let d := secondaryDDefectPolynomial68 Ae Be De
    Be.coeff (3 * n - g) = 0 ∨
      (60 ∣ n ∧ 60 ∣ g ∧
        Be.coeff (3 * n - g) ≠ 0 ∧
        ce.coeff (4 * n - g) ≠ 0 ∧
        d.coeff (5 * n - g - 60) ≠ 0 ∧
        ee.coeff (6 * n - g - 60) ≠ 0 ∧
        Ae.coeff (2 * n) * Be.coeff (3 * n - g) ^ 2 +
          3 * ce.coeff (4 * n - g) ^ 2 = 0 ∧
        d.coeff (5 * n - g - 90) = 0 ∧
        ee.coeff (6 * n - g - 90) = 0) := by
  let n := weightedRadius68 A B C0 D E
  let Ae := expand k 60 A
  let Be := expand k 60 B
  let Ce := expand k 60 C0
  let ce := cubicCDefectPolynomial68 Ae Ce
  let De := expand k 60 D
  let Ee := expand k 60 E
  let ee := cubicEDefectPolynomial68 Ae Ce Ee
  let g := cubicDefectGap68 n Be ce De ee
  let d := secondaryDDefectPolynomial68 Ae Be De
  change 3 * n ≤ 2 * g at hlater
  change n = 120 ∧ g = 360 at hwall
  change _ = 0 ∨ (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hp :=
    maximalExpandedIntegratedPolynomialLowerSystem_laterDeepOuter_offsetNinety_with_terminalRHS68
      l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
      hterminal hsys
      (by simpa only [n, Ae, Be, Ce, ce, De, Ee, ee, g] using hlater)
  change (((_ ∧ _ ∧ _) ∨ _) ∧
      ((_ ∧ _ ∧ _ ∧ _ ∧ _) ∨
        (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))) ∧ _ at hp
  rcases hp with ⟨hoffset, hadapter⟩
  rcases hoffset.2 with hzero | hnz
  · by_cases hbtop : Be.coeff (3 * n - g) = 0
    · exact Or.inl hbtop
    · let cu := cubicCDefectPolynomial68 A C0
      let du := secondaryDDefectPolynomial68 A B D
      let eu := cubicEDefectPolynomial68 A C0 E
      have hcexpand : ce = expand k 60 cu := by
        simpa only [ce, Ae, Ce, cu] using
          expand_cubicCDefectPolynomial68 60 A C0
      have hdexpand : d = expand k 60 du := by
        simpa only [d, Ae, Be, De, du] using
          secondaryDDefectPolynomial68_expand 60 A B D
      have heexpand : ee = expand k 60 eu := by
        simpa only [ee, Ae, Ce, Ee, eu] using
          expand_cubicEDefectPolynomial68 60 A C0 E
      have data :=
        maximalExpandedIntegratedPolynomialLowerSystem_laterDeepLoadI4Data68
          l alpha beta gamma delta epsilon zeta eta terminal A B C0 D E
          hterminal hsys
      change LaterDeepLoadI4Data68 l beta gamma delta epsilon zeta
        n g Ae Be ce De ee at data
      have hA4 : A.natDegree ≤ 4 := by
        have h := data.hA
        simp only [Ae, natDegree_expand, hwall.1] at h
        omega
      have hB0 : B.natDegree ≤ 0 := by
        have h := data.hB
        simp only [Be, natDegree_expand, hwall.1, hwall.2] at h
        omega
      have hc2 : cu.natDegree ≤ 2 := by
        have h := data.hc
        rw [hcexpand, natDegree_expand, hwall.1, hwall.2] at h
        omega
      have hd2 : du.natDegree ≤ 2 := by
        have h := hzero.2.2.1
        have h' : (expand k 60 du).natDegree ≤ 5 * n - g - 120 := by
          rw [← hdexpand]
          exact h
        rw [natDegree_expand, hwall.1, hwall.2] at h'
        omega
      have he4 : eu.natDegree ≤ 4 := by
        have h := hzero.2.2.2.1
        have h' : (expand k 60 eu).natDegree ≤ 6 * n - g - 120 := by
          rw [← heexpand]
          exact h
        rw [natDegree_expand, hwall.1, hwall.2] at h'
        omega
      have ha4 : A.coeff 4 ≠ 0 := by
        have h := data.ha
        simpa [Ae, hwall.1, coeff_expand] using h
      have hb0 : B.coeff 0 ≠ 0 := by
        simpa [Be, hwall.1, hwall.2, coeff_expand] using hbtop
      change FiveToSixTerminalRHSAdapter68 alpha gamma epsilon zeta eta
        terminal A B cu du eu at hadapter
      rcases hadapter with
        ⟨i4, i3, hi4, hi3, _hrow0, hrow1, hrow2, hrow0pos, _hiff⟩
      exact False.elim
        (fiveToSix_offsetOneTwenty_ordinary_positive_source_false68
          alpha gamma epsilon zeta eta i4 i3 A B cu du eu hA4 hB0 hc2
          hd2 he4 ha4 hb0 hi4 hi3 hrow0pos hrow1 hrow2)
  · exact Or.inr hnz

#print axioms fiveToSix_offsetTwoForty_ordinary_positive_source_closure68
#print axioms fiveToSix_offsetOneTwenty_ordinary_positive_source_false68
#print axioms maximalExpandedIntegratedPolynomialLowerSystem_offsetOneTwenty_ordinary_positive_reduction68

end LaterDeepLowerParentFiveToSixPositiveCoefficientSelector68

end Max11DegreeRoutes
