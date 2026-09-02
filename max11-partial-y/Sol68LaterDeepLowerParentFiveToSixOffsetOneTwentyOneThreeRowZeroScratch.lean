import Sol68LaterDeepLowerParentFiveToSixOffsetOneTwentySmallChartRowOneClosureScratch

/-! # The aligned `(N,G)=(1,3)` row-zero jet

The exact second-jet loads are `L=4*gamma*x` and `M=(9/2)*gamma*y`.
The contracted row-zero coefficient is `4`.
-/

noncomputable section

open Polynomial

namespace Max11DegreeRoutes

section LaterDeepLowerParentFiveToSixOffsetOneTwentyOneThreeRowZero68

variable {k : Type*} [Field k] [CharZero k]

set_option maxHeartbeats 30000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Exact homogeneous row-zero coefficient `4` in the `(1,3)` chart. -/
theorem secondaryResidualRowZeroPolynomial68_coeff_four_oneThreeChart68
    (A B c d e : k[X])
    (hA : A.natDegree ≤ 2) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 1) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 2) :
    (secondaryResidualRowZeroPolynomial68 A B c d e).coeff 4 =
      (-4 / 27 : k) * A.coeff 2 *
        (3 * A.coeff 1 * (B.coeff 0 * e.coeff 2 +
            c.coeff 1 * d.coeff 1) +
          2 * A.coeff 2 * (B.coeff 0 * e.coeff 1 +
            c.coeff 0 * d.coeff 1 + c.coeff 1 * d.coeff 0) +
          6 * d.coeff 1 * e.coeff 2) := by
  have hderA : (derivative A).natDegree ≤ 1 := by compute_degree; omega
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have h1 := coeff_mul_mul_mul_at_reflect_one68 A (derivative A) B e
    2 1 0 2 hA hderA hB he (by norm_num)
  norm_num [coeff_reflect, coeff_derivative] at h1
  rw [revAt_eq_self_of_lt (by norm_num : 0 < 1), hB1] at h1
  simp only [mul_zero, zero_mul, add_zero] at h1
  have h2 := coeff_mul_mul_mul_at_reflect_one68 A (derivative A) c d
    2 1 1 1 hA hderA hc hd (by norm_num)
  norm_num [coeff_reflect, coeff_derivative] at h2
  have h6 := coeff_mul_mul_at_bounds68 (derivative A) d e 1 1 2
    hderA hd he
  norm_num [coeff_derivative] at h6
  have hlow3 : (A * B ^ 2 * derivative d).natDegree < 4 := by
    compute_degree
    omega
  have hlow4 : (A * B * derivative B * d).natDegree < 4 := by
    compute_degree
    omega
  have hlow5 : (derivative A * B * c ^ 2).natDegree < 4 := by
    compute_degree
    omega
  have hlow7 : (B * c * derivative e).natDegree < 4 := by
    compute_degree
    omega
  have hlow8 : (B * d * derivative d).natDegree < 4 := by
    compute_degree
    omega
  have hlow9 : (derivative B * d ^ 2).natDegree < 4 := by
    compute_degree
    omega
  have hlow10 : (c * derivative c * d).natDegree < 4 := by
    compute_degree
    omega
  simp only [secondaryResidualRowZeroPolynomial68, coeff_smul, coeff_add,
    coeff_sub, h1, h2, h6,
    coeff_eq_zero_of_natDegree_lt hlow3,
    coeff_eq_zero_of_natDegree_lt hlow4,
    coeff_eq_zero_of_natDegree_lt hlow5,
    coeff_eq_zero_of_natDegree_lt hlow7,
    coeff_eq_zero_of_natDegree_lt hlow8,
    coeff_eq_zero_of_natDegree_lt hlow9,
    coeff_eq_zero_of_natDegree_lt hlow10, smul_eq_mul]
  ring

/-- With `zeta=0`, the contracted row-zero load at coefficient `4` is
exactly `-(4/9)*gamma*a^2*x`.  This is one step below the constant-`B`
top-load coefficient, so the gamma term must be retained. -/
theorem cubicLoadRowZeroPolynomial68_coeff_four_oneThreeChart68
    (alpha gamma epsilon eta : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 2) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 1) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 2) :
    (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c ((1 / 3 : k) • (A * B) + d) e).coeff 4 =
        (-4 / 9 : k) * gamma * A.coeff 2 ^ 2 * d.coeff 1 := by
  let D0 : k[X] := (1 / 3 : k) • (A * B) + d
  let E0 : k[X] :=
    (1 / 27 : k) • A ^ 3 + (1 / 3 : k) • (A * c) + e
  let Ur : k[X] := (2 / 3 * gamma : k) • B
  let W : k[X] :=
    (1 / 9 * gamma : k) • A ^ 2 + (2 / 3 * gamma : k) • c +
      (1 / 3 * epsilon : k) • A + C eta
  have hloadEq :
      cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
        A B c D0 e = Ur * derivative E0 - D0 * derivative W := by
    apply (FaithfulSMul.algebraMap_injective k[X] (RatFunc k))
    simp only [cubicLoadRowZeroPolynomial68, cubicLoadUPolynomial68,
      cubicLoadVPolynomial68, D0, E0, Ur, W,
      zero_mul, zero_smul, smul_zero, add_zero, zero_add, sub_zero,
      derivative_add, derivative_sub, derivative_mul, derivative_pow,
      derivative_smul, derivative_C, one_mul, Polynomial.smul_eq_C_mul,
      map_add, map_sub, map_mul, map_pow, map_neg, map_zero,
      RatFunc.algebraMap_C, map_div₀, map_ofNat, map_natCast, map_one]
    ring
  have hD : D0.natDegree ≤ 2 := by simp only [D0]; compute_degree; omega
  have hE : E0.natDegree ≤ 6 := by simp only [E0]; compute_degree; omega
  have hUr : Ur.natDegree ≤ 0 := by simp only [Ur]; compute_degree; omega
  have hW : W.natDegree ≤ 4 := by simp only [W]; compute_degree; omega
  have hderW : (derivative W).natDegree ≤ 3 := by compute_degree; omega
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hA3 := coeff_mul_mul_at_reflect_one68 A A A
    2 2 2 hA hA hA (by norm_num)
  norm_num [coeff_reflect] at hA3
  have hA3' : (A ^ 3).coeff 5 =
      3 * A.coeff 2 ^ 2 * A.coeff 1 := by
    rw [show A ^ 3 = A * A * A by ring]
    linear_combination hA3
  have hAclow : (A * c).natDegree < 5 := by compute_degree; omega
  have helow : e.natDegree < 5 := he.trans_lt (by norm_num)
  have hE5 : E0.coeff 5 =
      (1 / 9 : k) * A.coeff 2 ^ 2 * A.coeff 1 := by
    simp only [E0, coeff_add, coeff_smul, smul_eq_mul, hA3',
      coeff_eq_zero_of_natDegree_lt hAclow,
      coeff_eq_zero_of_natDegree_lt helow, mul_zero, add_zero]
    ring
  have hUrC : Ur = C (Ur.coeff 0) := eq_C_of_natDegree_le_zero hUr
  have hUr0 : Ur.coeff 0 = (2 / 3 * gamma : k) * B.coeff 0 := by
    simp only [Ur, coeff_smul, smul_eq_mul]
  have hUE : (Ur * derivative E0).coeff 4 =
      (10 / 27 : k) * gamma * B.coeff 0 *
        A.coeff 2 ^ 2 * A.coeff 1 := by
    rw [hUrC, C_mul', coeff_smul, coeff_derivative, hUr0, hE5]
    simp only [smul_eq_mul]
    ring
  have hAB2 := coeff_mul_at_bounds68 A B 2 0 hA hB
  norm_num at hAB2
  have hD2 : D0.coeff 2 =
      (1 / 3 : k) * A.coeff 2 * B.coeff 0 := by
    have hd2 : d.coeff 2 = 0 :=
      coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
    simp only [D0, coeff_add, coeff_smul, smul_eq_mul, hAB2, hd2]
    ring
  have hBC : B = C (B.coeff 0) := eq_C_of_natDegree_le_zero hB
  have hAB1 : (A * B).coeff 1 = A.coeff 1 * B.coeff 0 := by
    rw [hBC]
    simp
  have hD1 : D0.coeff 1 =
      (1 / 3 : k) * A.coeff 1 * B.coeff 0 + d.coeff 1 := by
    simp only [D0, coeff_add, coeff_smul, smul_eq_mul, hAB1]
    ring
  have hA2top := coeff_pow_at_bound68 A 2 2 hA
  norm_num at hA2top
  have hA2one := coeff_mul_mul_at_reflect_one68 A A (1 : k[X])
    2 2 0 hA hA (by norm_num) (by norm_num)
  norm_num [coeff_reflect, coeff_one] at hA2one
  have hc3 : c.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hA3zero : A.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by norm_num))
  have hW4 : W.coeff 4 =
      (1 / 9 * gamma : k) * A.coeff 2 ^ 2 := by
    simp only [W, coeff_add, coeff_smul, smul_eq_mul, hA2top,
      coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num : 1 < 4)),
      coeff_eq_zero_of_natDegree_lt (hA.trans_lt (by norm_num : 2 < 4)),
      coeff_C, if_neg (by norm_num : 4 ≠ 0), mul_zero, add_zero]
  have hW3 : W.coeff 3 =
      (2 / 9 : k) * gamma * A.coeff 2 * A.coeff 1 := by
    have hA2three : (A ^ 2).coeff 3 =
        2 * A.coeff 2 * A.coeff 1 := by
      rw [pow_two]
      linear_combination hA2one
    simp only [W, coeff_add, coeff_smul, smul_eq_mul, hA2three, hc3,
      hA3zero, coeff_C, if_neg (by norm_num : 3 ≠ 0), mul_zero,
      add_zero]
    ring
  have hDWraw := congrArg (fun p : k[X] => p.coeff 1)
    (reflect_mul D0 (derivative W) hD hderW)
  rw [mul_coeff_one] at hDWraw
  norm_num [coeff_reflect, coeff_derivative] at hDWraw
  have hDW : (D0 * derivative W).coeff 4 =
      (10 / 27 : k) * gamma * B.coeff 0 * A.coeff 2 ^ 2 *
          A.coeff 1 +
        (4 / 9 : k) * gamma * A.coeff 2 ^ 2 * d.coeff 1 := by
    rw [hD1, hD2, hW3, hW4] at hDWraw
    linear_combination hDWraw
  change (cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
      A B c D0 e).coeff 4 = _
  rw [hloadEq, coeff_sub, hUE, hDW]
  ring

/-- Row zero fixes the remaining gamma load without dividing by any
coefficient other than the already-nonzero old edge. -/
theorem fiveToSix_oneThree_rowZero_contradiction68
    (a a₁ b c c₀ x y u v gamma : k)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hface : b * y + c * x = 0)
    (hfour : (8 / 3 : k) * (b * v + c * u + c₀ * x) +
        4 * gamma * x = 0)
    (hrow : 3 * a₁ * (b * y + c * x) +
        2 * a * (b * v + c₀ * x + c * u) + 6 * x * y +
          3 * gamma * a * x = 0) : False := by
  have hprod : 6 * x * y = 0 := by
    linear_combination hrow - 3 * a₁ * hface - (3 / 4 : k) * a * hfour
  have hprod' : (6 : k) * (x * y) = 0 := by
    linear_combination hprod
  have hxy : x * y = 0 :=
    (mul_eq_zero.mp hprod').resolve_left (by norm_num)
  exact (mul_ne_zero hx hy) hxy

/-- Exact specialization of both second-jet first integrals to the aligned
`(N,G)=(1,3)` chart.  In particular the full loads are retained as
`L=4*gamma*x` and `M=(9/2)*gamma*y`. -/
theorem fiveToSix_aligned_secondJet_oneThree_source_packet68
    (gamma epsilon i4 i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 2) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 1) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 2)
    (hb : B.coeff 0 ≠ 0)
    (hface : B.coeff 0 * e.coeff 2 + c.coeff 1 * d.coeff 1 = 0)
    (hdisc : A.coeff 2 * B.coeff 0 ^ 2 + 3 * c.coeff 1 ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3) :
    ((8 / 3 : k) *
        (B.coeff 0 * e.coeff 1 + c.coeff 1 * d.coeff 0 +
          c.coeff 0 * d.coeff 1) + 4 * gamma * d.coeff 1 = 0) ∧
      (-A.coeff 2 * B.coeff 0 * d.coeff 0 -
          A.coeff 1 * B.coeff 0 * d.coeff 1 +
          3 * c.coeff 1 * e.coeff 1 +
          3 * c.coeff 0 * e.coeff 2 +
          (3 / 2 : k) * d.coeff 1 ^ 2 +
          (9 / 2 : k) * gamma * e.coeff 2 = 0) ∧
      4 * d.coeff 1 *
          (3 * B.coeff 0 * d.coeff 1 -
            2 * A.coeff 1 * B.coeff 0 ^ 2 -
            12 * c.coeff 1 * c.coeff 0) =
        36 * gamma * c.coeff 1 * d.coeff 1 -
          36 * gamma * B.coeff 0 * e.coeff 2 := by
  have hd2 : d.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by norm_num))
  have he3 : e.coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (he.trans_lt (by norm_num))
  have hB1 : B.coeff 1 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hB2 : B.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hB.trans_lt (by norm_num))
  have hc2 : c.coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hc.trans_lt (by norm_num))
  have hBsq : (B ^ 2).natDegree ≤ 0 := by compute_degree; omega
  have hBsq2 : (B ^ 2).coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (hBsq.trans_lt (by norm_num))
  have hd0 : (d.reflect 2).coeff 0 = 0 := by
    norm_num [coeff_reflect, hd2]
  have he0 : (e.reflect 3).coeff 0 = 0 := by
    norm_num [coeff_reflect, he3]
  have hbr : (B.reflect 0).coeff 0 ≠ 0 := by
    simpa only [coeff_reflect, revAt_zero] using hb
  have hfaceR : (B.reflect 0).coeff 0 * (e.reflect 3).coeff 1 +
      (c.reflect 1).coeff 0 * (d.reflect 2).coeff 1 = 0 := by
    norm_num [coeff_reflect]
    exact hface
  have hdiscR : (A.reflect 2).coeff 0 * (B.reflect 0).coeff 0 ^ 2 +
      3 * (c.reflect 1).coeff 0 ^ 2 = 0 := by
    norm_num [coeff_reflect]
    exact hdisc
  have hp := fiveToSix_aligned_secondJet_source_packet68
    gamma epsilon 0 i4 i3 A B c d e 1 3 (by norm_num) (by norm_num)
    hA hB hc (hd.trans (by norm_num)) (he.trans (by norm_num))
    hd0 he0 hbr hfaceR hdiscR hi4 hi3
  dsimp only at hp
  norm_num [coeff_reflect, hd2, he3, hB1, hB2, hc2, hBsq2] at hp
  rw [revAt_eq_self_of_lt (by norm_num : 0 < 1), hB1, zero_mul,
    add_zero] at hp
  obtain ⟨hfour, hthree, hcompat⟩ := hp
  simp only [mul_zero, zero_mul, add_zero, zero_add, sub_zero] at hfour hthree hcompat
  constructor
  · linear_combination hfour
  constructor
  · linear_combination hthree
  · linear_combination hcompat

set_option maxHeartbeats 15000000 in
/-- Coefficient `4` of the exact row-zero source closes the remaining
aligned `(1,3)` lower-load chart.  The contracted gamma load cancels the
literal I4 load, leaving the forbidden product `x*y`. -/
theorem fiveToSix_aligned_secondJet_oneThree_rowZero_source_false68
    (alpha gamma epsilon eta i4 i3 : k) (A B c d e : k[X])
    (hA : A.natDegree ≤ 2) (hB : B.natDegree ≤ 0)
    (hc : c.natDegree ≤ 1) (hd : d.natDegree ≤ 1)
    (he : e.natDegree ≤ 2)
    (ha : A.coeff 2 ≠ 0) (hb : B.coeff 0 ≠ 0)
    (hx : d.coeff 1 ≠ 0) (hy : e.coeff 2 ≠ 0)
    (hface : B.coeff 0 * e.coeff 2 + c.coeff 1 * d.coeff 1 = 0)
    (hdisc : A.coeff 2 * B.coeff 0 ^ 2 + 3 * c.coeff 1 ^ 2 = 0)
    (hi4 : cubicFirstIntegralFourPolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i4)
    (hi3 : cubicFirstIntegralThreePolynomial68 0 0 gamma 0 epsilon 0
        A B c ((1 / 3 : k) • (A * B) + d) e = C i3)
    (hrow : (secondaryResidualRowZeroPolynomial68 A B c d e +
        cubicLoadRowZeroPolynomial68 0 alpha 0 gamma 0 epsilon 0 eta
          A B c ((1 / 3 : k) • (A * B) + d) e).coeff 4 = 0) : False := by
  have hp := fiveToSix_aligned_secondJet_oneThree_source_packet68
    gamma epsilon i4 i3 A B c d e hA hB hc hd he hb hface hdisc hi4 hi3
  obtain ⟨hfour, _hthree, _hcompat⟩ := hp
  have hres := secondaryResidualRowZeroPolynomial68_coeff_four_oneThreeChart68
    A B c d e hA hB hc hd he
  have hload := cubicLoadRowZeroPolynomial68_coeff_four_oneThreeChart68
    alpha gamma epsilon eta A B c d e hA hB hc hd he
  rw [coeff_add, hres, hload] at hrow
  have hfact : (-4 / 27 : k) * A.coeff 2 *
      (3 * A.coeff 1 *
          (B.coeff 0 * e.coeff 2 + c.coeff 1 * d.coeff 1) +
        2 * A.coeff 2 *
          (B.coeff 0 * e.coeff 1 + c.coeff 0 * d.coeff 1 +
            c.coeff 1 * d.coeff 0) +
        6 * d.coeff 1 * e.coeff 2 +
        3 * gamma * A.coeff 2 * d.coeff 1) = 0 := by
    linear_combination hrow
  have hscalar :
      3 * A.coeff 1 *
          (B.coeff 0 * e.coeff 2 + c.coeff 1 * d.coeff 1) +
        2 * A.coeff 2 *
          (B.coeff 0 * e.coeff 1 + c.coeff 0 * d.coeff 1 +
            c.coeff 1 * d.coeff 0) +
        6 * d.coeff 1 * e.coeff 2 +
        3 * gamma * A.coeff 2 * d.coeff 1 = 0 := by
    exact (mul_eq_zero.mp hfact).resolve_left
      (mul_ne_zero (by norm_num) ha)
  exact fiveToSix_oneThree_rowZero_contradiction68
    (A.coeff 2) (A.coeff 1) (B.coeff 0) (c.coeff 1) (c.coeff 0)
    (d.coeff 1) (e.coeff 2) (d.coeff 0) (e.coeff 1) gamma
    hx hy hface hfour hscalar

#print axioms secondaryResidualRowZeroPolynomial68_coeff_four_oneThreeChart68
#print axioms cubicLoadRowZeroPolynomial68_coeff_four_oneThreeChart68
#print axioms fiveToSix_oneThree_rowZero_contradiction68
#print axioms fiveToSix_aligned_secondJet_oneThree_source_packet68
#print axioms fiveToSix_aligned_secondJet_oneThree_rowZero_source_false68

end LaterDeepLowerParentFiveToSixOffsetOneTwentyOneThreeRowZero68

end Max11DegreeRoutes
