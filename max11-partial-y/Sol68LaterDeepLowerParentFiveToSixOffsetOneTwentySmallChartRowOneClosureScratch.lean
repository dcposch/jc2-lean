import Sol68LaterDeepLowerParentFiveToSixOffsetOneTwentySmallChartScratch

/-! # Row-one closure of the aligned offset-120 small chart

Coefficient `10` is deliberately skipped: it is the first-edge row and is
already a scalar multiple of I3.  Coefficient `9` is the second row-one jet.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneTwentySmallChartRowOne68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- First reflected jet of a product of three bounded polynomials. -/
theorem coeff_mul_mul_at_reflect_one68
    (p q r : k[X]) (u v w : ℕ)
    (hp : p.natDegree ≤ u) (hq : q.natDegree ≤ v)
    (hr : r.natDegree ≤ w) (hsum : 1 ≤ u + v + w) :
    (p * q * r).coeff (u + v + w - 1) =
      (p.reflect u).coeff 0 * (q.reflect v).coeff 0 *
          (r.reflect w).coeff 1 +
        (p.reflect u).coeff 0 * (q.reflect v).coeff 1 *
          (r.reflect w).coeff 0 +
        (p.reflect u).coeff 1 * (q.reflect v).coeff 0 *
          (r.reflect w).coeff 0 := by
  have hpq : (p * q).natDegree ≤ u + v :=
    natDegree_mul_le_of_le hp hq
  have h := congrArg (fun t : k[X] => t.coeff 1)
    (reflect_mul (p * q) r hpq hr)
  rw [coeff_reflect, revAt_le hsum, mul_coeff_one,
    reflect_mul p q hp hq, mul_coeff_zero, mul_coeff_one] at h
  linear_combination h

/-- Exact homogeneous row-one coefficient `9` in the `(2,6)` chart. -/
theorem secondaryResidualRowOnePolynomial68_coeff_nine_smallChart68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 3)
    (he : e.natDegree ≤ 5) :
    (secondaryResidualRowOnePolynomial68 A B c d e).coeff 9 =
      (-4 / 27 : k) *
        (12 * A.coeff 4 ^ 2 * B.coeff 0 * d.coeff 2 +
          26 * A.coeff 4 * A.coeff 3 * B.coeff 0 * d.coeff 3 -
          42 * A.coeff 3 * c.coeff 2 * e.coeff 5 -
          36 * A.coeff 4 * c.coeff 1 * e.coeff 5 -
          36 * A.coeff 4 * c.coeff 2 * e.coeff 4 +
          12 * A.coeff 4 * d.coeff 3 ^ 2 -
          90 * e.coeff 5 ^ 2) := by
  have hderA : (derivative A).natDegree ≤ 3 := by compute_degree; omega
  have hderd : (derivative d).natDegree ≤ 2 := by compute_degree; omega
  have hderc : (derivative c).natDegree ≤ 1 := by compute_degree; omega
  have hdere : (derivative e).natDegree ≤ 4 := by compute_degree; omega
  have hderB : derivative B = 0 := by
    apply derivative_eq_zero.mpr
    omega
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have h1 := coeff_mul_mul_mul_at_reflect_one68 A A B (derivative d)
    4 4 0 2 hA hA hB hderd (by norm_num)
  norm_num [coeff_reflect, coeff_derivative] at h1
  rw [revAt_eq_self_of_lt (by norm_num : 0 < 1), hB1] at h1
  simp only [mul_zero, zero_mul, add_zero] at h1
  have h1' : (A * A * B * derivative d).coeff 9 =
      2 * A.coeff 4 ^ 2 * B.coeff 0 * d.coeff 2 +
        6 * A.coeff 4 * A.coeff 3 * B.coeff 0 * d.coeff 3 := by
    linear_combination h1
  have h1pow : (A ^ 2 * B * derivative d).coeff 9 =
      2 * A.coeff 4 ^ 2 * B.coeff 0 * d.coeff 2 +
        6 * A.coeff 4 * A.coeff 3 * B.coeff 0 * d.coeff 3 := by
    simpa only [pow_two, mul_assoc] using h1'
  have h3 := coeff_mul_mul_mul_at_reflect_one68 A (derivative A) B d
    4 3 0 3 hA hderA hB hd (by norm_num)
  norm_num [coeff_reflect, coeff_derivative] at h3
  rw [revAt_eq_self_of_lt (by norm_num : 0 < 1), hB1] at h3
  simp only [mul_zero, zero_mul, add_zero] at h3
  have h3' : (A * derivative A * B * d).coeff 9 =
      4 * A.coeff 4 ^ 2 * B.coeff 0 * d.coeff 2 +
        7 * A.coeff 4 * A.coeff 3 * B.coeff 0 * d.coeff 3 := by
    linear_combination h3
  have h4 := coeff_mul_mul_at_reflect_one68 A c (derivative e)
    4 2 4 hA hc hdere (by norm_num)
  norm_num [coeff_reflect, coeff_derivative] at h4
  have h4' : (A * c * derivative e).coeff 9 =
      5 * A.coeff 3 * c.coeff 2 * e.coeff 5 +
        5 * A.coeff 4 * c.coeff 1 * e.coeff 5 +
        4 * A.coeff 4 * c.coeff 2 * e.coeff 4 := by
    linear_combination h4
  have h5 := coeff_mul_mul_at_reflect_one68 A (derivative c) e
    4 1 5 hA hderc he (by norm_num)
  norm_num [coeff_reflect, coeff_derivative] at h5
  have h5' : (A * derivative c * e).coeff 9 =
      2 * A.coeff 3 * c.coeff 2 * e.coeff 5 +
        A.coeff 4 * c.coeff 1 * e.coeff 5 +
        2 * A.coeff 4 * c.coeff 2 * e.coeff 4 := by
    linear_combination h5
  have h7 := coeff_mul_mul_at_bounds68 (derivative A) d d 3 3 3
    hderA hd hd
  norm_num [coeff_derivative] at h7
  have h7' : (derivative A * d * d).coeff 9 =
      4 * A.coeff 4 * d.coeff 3 ^ 2 := by
    linear_combination h7
  have h7pow : (derivative A * d ^ 2).coeff 9 =
      4 * A.coeff 4 * d.coeff 3 ^ 2 := by
    simpa only [pow_two, mul_assoc] using h7'
  have h13 := coeff_mul_at_bounds68 e (derivative e) 5 4 he hdere
  norm_num [coeff_derivative] at h13
  have h13' : (e * derivative e).coeff 9 = 5 * e.coeff 5 ^ 2 := by
    linear_combination h13
  have hlow2 : (A ^ 2 * derivative B * d).natDegree < 9 := by
    rw [hderB, mul_zero, zero_mul, natDegree_zero]
    norm_num
  have hlow6 : (derivative A * B ^ 2 * c).natDegree < 9 := by
    compute_degree
    omega
  have hlow8 : (B ^ 2 * derivative e).natDegree < 9 := by
    compute_degree
    omega
  have hlow9 : (B * c * derivative d).natDegree < 9 := by
    compute_degree
    omega
  have hlow10 : (B * derivative c * d).natDegree < 9 := by
    compute_degree
    omega
  have hlow11 : (derivative B * c * d).natDegree < 9 := by
    compute_degree
    omega
  have hlow12 : (c ^ 2 * derivative c).natDegree < 9 := by
    compute_degree
    omega
  simp only [secondaryResidualRowOnePolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1pow, h3', h4', h5', h7pow, h13',
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow6,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9,
    coeff_eq_zero_of_natDegree_lt hlow10,
    coeff_eq_zero_of_natDegree_lt hlow11,
    coeff_eq_zero_of_natDegree_lt hlow12, smul_eq_mul]
  ring

/-- After cancellation of the alpha pieces, the row-one load has degree
strictly below `9`; hence coefficient `9` is genuinely load-free. -/
theorem cubicLoadRowOnePolynomial68_coeff_nine_smallChart68
    (alpha gamma epsilon zeta eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 3)
    (he : e.natDegree ≤ 5) :
    (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 9 = 0 := by
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  let Ur : k[X] := (2 / 3 * gamma : k) • B + C zeta
  have hloadEq :
      cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
        A B c D0 e =
      Ur * derivative D0 +
        (4 / 3 * gamma : k) • (A * derivative e - c * derivative c) +
        (2 / 3 * epsilon : k) • (A * derivative c) +
        (2 * epsilon : k) • derivative e -
        (2 / 3 * gamma : k) • (D0 * derivative B) := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicLoadRowOnePolynomial68, cubicLoadTPolynomial68,
      cubicLoadUPolynomial68, cubicLoadVPolynomial68, D0, Ur,
      zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
      derivative_add, derivative_sub, derivative_mul, derivative_pow,
      derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
      map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hD : D0.natDegree ≤ 4 := by
    simp only [D0]
    compute_degree
    omega
  have hUr : Ur.natDegree ≤ 0 := by
    simp only [Ur]
    compute_degree
    omega
  have hlow1 : (Ur * derivative D0).natDegree < 9 := by
    compute_degree
    omega
  have hlow2 : ((4 / 3 * gamma : k) •
      (A * derivative e - c * derivative c)).natDegree < 9 := by
    compute_degree
    omega
  have hlow3 : ((2 / 3 * epsilon : k) •
      (A * derivative c)).natDegree < 9 := by
    compute_degree
    omega
  have hlow4 : ((2 * epsilon : k) • derivative e).natDegree < 9 := by
    compute_degree
    omega
  have hlow5 : ((2 / 3 * gamma : k) •
      (D0 * derivative B)).natDegree < 9 := by
    compute_degree
    omega
  change (cubicLoadRowOnePolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
      A B c D0 e).coeff 9 = 0
  rw [hloadEq, coeff_sub, coeff_add, coeff_add, coeff_add,
    coeff_eq_zero_of_natDegree_lt hlow1,
    coeff_eq_zero_of_natDegree_lt hlow2,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5]
  ring

/-- The degree-`9` row-one scalar contradicts the old nonzero edge face. -/
theorem fiveToSix_smallChart_rowOne_nine_contradiction68
    (a a₁ b c c₁ x y u v : k)
    (hc : c ≠ 0) (hy : y ≠ 0)
    (hface : b * y + c * x = 0)
    (hthree0 : -a * b * x + 3 * c * y = 0)
    (hdisc : a * b ^ 2 + 3 * c ^ 2 = 0)
    (hthree : -a * b * u - a₁ * b * x + 3 * c * v +
        3 * c₁ * y + (3 / 2 : k) * x ^ 2 = 0)
    (hrow : 12 * a ^ 2 * b * u + 26 * a * a₁ * b * x -
        42 * a₁ * c * y - 36 * a * c₁ * y - 36 * a * c * v +
        12 * a * x ^ 2 - 90 * y ^ 2 = 0) : False := by
  have hfaceSq : b ^ 2 * y ^ 2 - c ^ 2 * x ^ 2 = 0 := by
    linear_combination (b * y - c * x) * hface
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hquadProd : c ^ 2 * (a * x ^ 2 + 3 * y ^ 2) = 0 := by
    linear_combination y ^ 2 * hdisc - a * hfaceSq
  have hquad : a * x ^ 2 + 3 * y ^ 2 = 0 :=
    (mul_eq_zero.mp hquadProd).resolve_left hc2
  have hyScaled : (-180 : k) * y ^ 2 = 0 := by
    linear_combination hrow + 12 * a * hthree +
      14 * a₁ * hthree0 - 30 * hquad
  have hySq : y ^ 2 = 0 :=
    (mul_eq_zero.mp hyScaled).resolve_left (by norm_num)
  exact (pow_ne_zero 2 hy) hySq

set_option maxHeartbeats 15000000 in
/-- Literal integrated-row-one closure of the aligned `(N,G)=(2,6)` lane.
The predecessor's row-zero packet supplies the exact second-jet I3 scalar;
row-one coefficient `9` then forces the nonzero coefficient `e₅` to vanish. -/
theorem fiveToSix_aligned_secondJet_smallChart_rowOne_source_false68
    (alpha gamma epsilon zeta eta i4 i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 4) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 2) (hd : d.natDegree ≤ 3)
    (he : e.natDegree ≤ 5)
    (ha : A.coeff 4 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hcTop : c.coeff 2 ≠ 0)
    (hx : d.coeff 3 ≠ 0) (hy : e.coeff 5 ≠ 0)
    (hface : B.coeff 0 * e.coeff 5 + c.coeff 2 * d.coeff 3 = 0)
    (hdisc : A.coeff 4 * B.coeff 0 ^ 2 + 3 * c.coeff 2 ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon zeta
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrowZero : (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon zeta eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 11 = 0)
    (hrowOne :
      let C0 := (1 / 3 : k) • A ^ 2 + c
      let D0 := (1 / 3 : k) • (A * B) + d
      let E0 := (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
      lowerRowOnePolynomial68
        (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D0 E0)
        (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B C0 D0 E0)
        (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
          A B C0 D0 E0) C0 D0 E0 = 0) : False := by
  let C0 : k[X] := (1 / 3 : k) • A ^ 2 + c
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  let E0 : k[X] :=
    (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  change lowerRowOnePolynomial68
      (integratedTPolynomial68 0 alpha 0 gamma epsilon A B C0 D0 E0)
      (integratedUPolynomial68 0 alpha 0 gamma 0 zeta A B C0 D0 E0)
      (integratedVPolynomial68 0 alpha 0 gamma 0 epsilon eta
        A B C0 D0 E0) C0 D0 E0 = 0 at hrowOne
  have hsmall := fiveToSix_aligned_secondJet_smallChart_source_packet68
    alpha gamma epsilon zeta eta i4 i3 A B c d e
    hA hB hc hd he ha hb hx hy hface hdisc hi4 hi3 hrowZero
  obtain ⟨_hfour, hthree, _hzetaEdge, _hzeta, _hjet⟩ := hsmall
  have hthree0 : -A.coeff 4 * B.coeff 0 * d.coeff 3 +
      3 * c.coeff 2 * e.coeff 5 = 0 := by
    have hbthree : B.coeff 0 *
        (-A.coeff 4 * B.coeff 0 * d.coeff 3 +
          3 * c.coeff 2 * e.coeff 5) = 0 := by
      linear_combination -d.coeff 3 * hdisc + 3 * c.coeff 2 * hface
    exact (mul_eq_zero.mp hbthree).resolve_left hb
  have hcoords := integratedPolynomial68_cubicCoordinates
    (0 : k) alpha 0 gamma 0 epsilon zeta eta A B c D0 e
  have hrowCoeff := congrArg (fun p : k[X] => p.coeff 9) hrowOne
  have hhom : cubicHomogeneousRowOnePolynomial68 A B c D0 e =
      secondaryResidualRowOnePolynomial68 A B c d e := by
    simpa only [D0] using
      cubicHomogeneousRowOnePolynomial68_residualCoordinates A B c d e
  have hres := secondaryResidualRowOnePolynomial68_coeff_nine_smallChart68
    A B c d e hA hB hc hd he
  have hload := cubicLoadRowOnePolynomial68_coeff_nine_smallChart68
    alpha gamma epsilon zeta eta A B c d e hA hB hc hd he
  rw [hcoords.t_eq, hcoords.u_eq, hcoords.v_eq,
    cubicRowOnePolynomial68_split, coeff_add, hhom, hres, hload,
    add_zero] at hrowCoeff
  simp only [coeff_zero] at hrowCoeff
  have hrow :
      12 * A.coeff 4 ^ 2 * B.coeff 0 * d.coeff 2 +
        26 * A.coeff 4 * A.coeff 3 * B.coeff 0 * d.coeff 3 -
        42 * A.coeff 3 * c.coeff 2 * e.coeff 5 -
        36 * A.coeff 4 * c.coeff 1 * e.coeff 5 -
        36 * A.coeff 4 * c.coeff 2 * e.coeff 4 +
        12 * A.coeff 4 * d.coeff 3 ^ 2 -
        90 * e.coeff 5 ^ 2 = 0 := by
    have hnz : (-4 / 27 : k) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hrowCoeff).resolve_left hnz
  exact fiveToSix_smallChart_rowOne_nine_contradiction68
    (A.coeff 4) (A.coeff 3) (B.coeff 0) (c.coeff 2) (c.coeff 1)
    (d.coeff 3) (e.coeff 5) (d.coeff 2) (e.coeff 4)
    hcTop hy hface hthree0 hdisc hthree hrow

#print axioms coeff_mul_mul_at_reflect_one68
#print axioms secondaryResidualRowOnePolynomial68_coeff_nine_smallChart68
#print axioms cubicLoadRowOnePolynomial68_coeff_nine_smallChart68
#print axioms fiveToSix_smallChart_rowOne_nine_contradiction68
#print axioms fiveToSix_aligned_secondJet_smallChart_rowOne_source_false68

end LaterDeepLowerParentFiveToSixOffsetOneTwentySmallChartRowOne68

end Max11DegreeRoutes
